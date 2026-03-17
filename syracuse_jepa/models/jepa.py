"""
Collatz-JEPA — Joint Embedding Predictive Architecture for Collatz Junction Theorem

Architecture:
  Context Encoder: processes View 1 (composition structure + FFT)
  Target Encoder:  processes View 2 (arithmetic properties + residues)
  Predictor:       predicts target representation from context representation

The key idea: the JEPA learns WHY certain arithmetic properties (View 2)
follow from the composition structure (View 1). The latent space captures
the mathematical relationship between compositions and their corrSum.

The Target Encoder is an EMA (Exponential Moving Average) of the Context
Encoder — this is the standard I-JEPA setup from Assran et al. (2023).
"""

import copy
import torch
import torch.nn as nn


class CompositionEncoder(nn.Module):
    """
    Encodes a composition and its features into a latent representation.

    Input: composition features (padded to max_k)
    Output: latent vector of dim embed_dim
    """

    def __init__(self, max_k: int = 50, embed_dim: int = 128, n_primes: int = 11):
        super().__init__()
        self.max_k = max_k
        self.embed_dim = embed_dim

        # Composition branch: 1D convolutions over the sequence
        self.conv1 = nn.Conv1d(1, 32, kernel_size=3, padding=1)
        self.conv2 = nn.Conv1d(32, 64, kernel_size=3, padding=1)
        self.conv3 = nn.Conv1d(64, 64, kernel_size=3, padding=1)

        # FFT branch: processes spectral features
        self.fft_branch = nn.Sequential(
            nn.Linear(max_k * 2, 128),  # magnitude + phase
            nn.GELU(),
            nn.Linear(128, 64),
            nn.GELU(),
        )

        # Prime residues branch
        self.prime_branch = nn.Sequential(
            nn.Linear(n_primes, 32),
            nn.GELU(),
            nn.Linear(32, 32),
            nn.GELU(),
        )

        # Merge all branches
        self.merge = nn.Sequential(
            nn.Linear(64 * max_k + 64 + 32 + 1, 256),  # +1 for fractional_ratio
            nn.GELU(),
            nn.LayerNorm(256),
            nn.Linear(256, embed_dim),
            nn.GELU(),
            nn.LayerNorm(embed_dim),
        )

    def forward(
        self,
        composition: torch.Tensor,     # (B, max_k)
        fft_magnitude: torch.Tensor,    # (B, max_k)
        fft_phase: torch.Tensor,        # (B, max_k)
        prime_residues: torch.Tensor,   # (B, n_primes)
        fractional_ratio: torch.Tensor, # (B,)
    ) -> torch.Tensor:
        B = composition.shape[0]

        # Composition convolutions
        x_comp = composition.unsqueeze(1)  # (B, 1, max_k)
        x_comp = torch.relu(self.conv1(x_comp))
        x_comp = torch.relu(self.conv2(x_comp))
        x_comp = torch.relu(self.conv3(x_comp))
        x_comp = x_comp.reshape(B, -1)  # (B, 64 * max_k)

        # FFT branch
        x_fft = torch.cat([fft_magnitude, fft_phase], dim=-1)  # (B, 2*max_k)
        x_fft = self.fft_branch(x_fft)  # (B, 64)

        # Prime residues
        x_primes = self.prime_branch(prime_residues)  # (B, 32)

        # Merge
        x = torch.cat([x_comp, x_fft, x_primes, fractional_ratio.unsqueeze(-1)], dim=-1)
        z = self.merge(x)

        return z  # (B, embed_dim)


class Predictor(nn.Module):
    """
    Predicts target representation from context representation.
    Narrow architecture (smaller than encoder) — standard JEPA design.
    """

    def __init__(self, embed_dim: int = 128, hidden_dim: int = 256):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(embed_dim, hidden_dim),
            nn.GELU(),
            nn.LayerNorm(hidden_dim),
            nn.Linear(hidden_dim, hidden_dim),
            nn.GELU(),
            nn.LayerNorm(hidden_dim),
            nn.Linear(hidden_dim, embed_dim),
        )

    def forward(self, z_context: torch.Tensor) -> torch.Tensor:
        return self.net(z_context)


class CollatzJEPA(nn.Module):
    """
    Full JEPA model for Collatz Junction Theorem.

    The two views:
      Context view: composition + FFT (structural properties)
      Target view:  composition + prime residues + fractional ratio (arithmetic properties)

    Both encoders see overlapping features, but with different emphasis.
    The context encoder focuses on STRUCTURE, the target on ARITHMETIC.
    The predictor must learn the mathematical bridge between the two.

    The target encoder is an EMA of the context encoder.
    """

    def __init__(
        self,
        max_k: int = 50,
        embed_dim: int = 128,
        predictor_hidden: int = 256,
        ema_decay: float = 0.996,
        n_primes: int = 11,
    ):
        super().__init__()
        self.max_k = max_k
        self.embed_dim = embed_dim
        self.ema_decay = ema_decay

        # Context encoder (trainable)
        self.context_encoder = CompositionEncoder(max_k, embed_dim, n_primes)

        # Target encoder (EMA copy — NOT trainable directly)
        self.target_encoder = copy.deepcopy(self.context_encoder)
        for param in self.target_encoder.parameters():
            param.requires_grad = False

        # Predictor
        self.predictor = Predictor(embed_dim, predictor_hidden)

    @torch.no_grad()
    def update_target_encoder(self):
        """Update target encoder as EMA of context encoder."""
        for param_t, param_c in zip(
            self.target_encoder.parameters(),
            self.context_encoder.parameters(),
        ):
            param_t.data.mul_(self.ema_decay).add_(param_c.data, alpha=1.0 - self.ema_decay)

    def forward(self, batch: dict) -> dict:
        """
        Forward pass.

        The context view emphasizes structure (composition + FFT).
        The target view emphasizes arithmetic (composition + primes + ratio).
        Both see the composition but with different "masks":
          - Context: FFT features are primary, prime residues are secondary
          - Target: Prime residues and ratio are primary, FFT is secondary

        In practice, both encoders have same architecture but different weights
        (EMA). The ASYMMETRY comes from the predictor, which must bridge
        context→target.
        """
        comp = batch['composition']
        fft_mag = batch['fft_magnitude']
        fft_phase = batch['fft_phase']
        primes = batch['prime_residues']
        frac_ratio = batch['fractional_ratio']

        # Context encoding (with gradients)
        z_context = self.context_encoder(comp, fft_mag, fft_phase, primes, frac_ratio)

        # Prediction
        z_pred = self.predictor(z_context)

        # Target encoding (no gradients — EMA network)
        with torch.no_grad():
            z_target = self.target_encoder(comp, fft_mag, fft_phase, primes, frac_ratio)

        return {
            'z_context': z_context,
            'z_pred': z_pred,
            'z_target': z_target,
        }

    def encode(self, batch: dict) -> torch.Tensor:
        """Encode a batch using the context encoder (for analysis)."""
        return self.context_encoder(
            batch['composition'],
            batch['fft_magnitude'],
            batch['fft_phase'],
            batch['prime_residues'],
            batch['fractional_ratio'],
        )

    def count_parameters(self) -> dict:
        """Count model parameters."""
        ctx = sum(p.numel() for p in self.context_encoder.parameters())
        pred = sum(p.numel() for p in self.predictor.parameters())
        return {
            'context_encoder': ctx,
            'target_encoder': ctx,  # same architecture
            'predictor': pred,
            'total_trainable': ctx + pred,
        }
