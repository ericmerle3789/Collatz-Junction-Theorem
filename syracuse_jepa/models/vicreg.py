"""
VICReg Loss — Variance, Invariance, Covariance Regularization

Reference: Bardes, Ponce, LeCun (2022) "VICReg: Variance-Invariance-Covariance
Regularization for Self-Supervised Learning"

Prevents representation collapse in JEPA by enforcing:
- Variance: each dimension of the embedding must have variance >= threshold
- Invariance: embeddings of different views should be similar
- Covariance: decorrelation between embedding dimensions
"""

import torch
import torch.nn.functional as F


class VICRegLoss(torch.nn.Module):
    """
    VICReg loss for Collatz-JEPA.

    Args:
        lambda_inv: Weight for invariance (MSE between predicted and target)
        lambda_var: Weight for variance regularization
        lambda_cov: Weight for covariance regularization
        var_threshold: Target standard deviation for each dimension
    """

    def __init__(
        self,
        lambda_inv: float = 25.0,
        lambda_var: float = 25.0,
        lambda_cov: float = 1.0,
        var_threshold: float = 1.0,
    ):
        super().__init__()
        self.lambda_inv = lambda_inv
        self.lambda_var = lambda_var
        self.lambda_cov = lambda_cov
        self.var_threshold = var_threshold

    def variance_loss(self, z: torch.Tensor) -> torch.Tensor:
        """Encourage variance in each embedding dimension."""
        std = torch.sqrt(z.var(dim=0) + 1e-4)
        return F.relu(self.var_threshold - std).mean()

    def covariance_loss(self, z: torch.Tensor) -> torch.Tensor:
        """Decorrelate embedding dimensions."""
        N, D = z.shape
        z_centered = z - z.mean(dim=0)
        cov = (z_centered.T @ z_centered) / (N - 1)
        # Zero out diagonal (we want off-diagonal to be small)
        off_diag = cov - torch.diag(cov.diag())
        return (off_diag ** 2).sum() / D

    def invariance_loss(self, z_pred: torch.Tensor, z_target: torch.Tensor) -> torch.Tensor:
        """MSE between predicted and target representations."""
        return F.mse_loss(z_pred, z_target)

    def forward(self, z_pred: torch.Tensor, z_target: torch.Tensor) -> dict:
        """
        Compute VICReg loss.

        Args:
            z_pred: Predicted representations from context encoder + predictor
            z_target: Target representations from target encoder (stop-gradient)

        Returns:
            dict with total loss and components
        """
        inv_loss = self.invariance_loss(z_pred, z_target.detach())
        var_loss_pred = self.variance_loss(z_pred)
        var_loss_target = self.variance_loss(z_target)
        var_loss = (var_loss_pred + var_loss_target) / 2
        cov_loss_pred = self.covariance_loss(z_pred)
        cov_loss_target = self.covariance_loss(z_target)
        cov_loss = (cov_loss_pred + cov_loss_target) / 2

        total = (
            self.lambda_inv * inv_loss
            + self.lambda_var * var_loss
            + self.lambda_cov * cov_loss
        )

        return {
            'loss': total,
            'invariance': inv_loss.item(),
            'variance': var_loss.item(),
            'covariance': cov_loss.item(),
        }
