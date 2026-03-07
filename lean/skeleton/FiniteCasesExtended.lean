import FiniteCases

/-!
# Extended Finite Case Verification (k ∈ [201, 306])

Extends `crystal_nonsurjectivity_le_200` to cover k up to 306 (= q₇, the 7th
convergent denominator of log₂3). This pushes the sorry boundary from k ≥ 201
to k ≥ 307, past the critical convergent q₇ = 306.

## Compilation Note

This file uses `native_decide` on integers up to ~2^485 (k = 306, S = 485).
Expected compilation time: 5–15 minutes depending on hardware.
GMP-backed arbitrary precision arithmetic handles all computations.
-/

namespace Collatz.FiniteCases

open Real Nat

/-- Crystal nonsurjectivity for k ∈ [201, 306]. -/
theorem crystal_nonsurjectivity_201_306 (k : ℕ) (hk : k ≥ 201) (hk_le : k ≤ 306)
    (S : ℕ) (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0) :
    Nat.choose (S - 1) (k - 1) < (crystalModule S k).toNat := by
  interval_cases k
  · exact close_case 201 319 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 202 321 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 203 322 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 204 324 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 205 325 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 206 327 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 207 329 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 208 330 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 209 332 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 210 333 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 211 335 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 212 337 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 213 338 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 214 340 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 215 341 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 216 343 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 217 344 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 218 346 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 219 348 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 220 349 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 221 351 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 222 352 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 223 354 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 224 356 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 225 357 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 226 359 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 227 360 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 228 362 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 229 363 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 230 365 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 231 367 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 232 368 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 233 370 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 234 371 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 235 373 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 236 375 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 237 376 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 238 378 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 239 379 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 240 381 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 241 382 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 242 384 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 243 386 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 244 387 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 245 389 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 246 390 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 247 392 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 248 394 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 249 395 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 250 397 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 251 398 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 252 400 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 253 401 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 254 403 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 255 405 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 256 406 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 257 408 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 258 409 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 259 411 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 260 413 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 261 414 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 262 416 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 263 417 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 264 419 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 265 421 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 266 422 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 267 424 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 268 425 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 269 427 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 270 428 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 271 430 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 272 432 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 273 433 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 274 435 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 275 436 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 276 438 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 277 440 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 278 441 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 279 443 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 280 444 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 281 446 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 282 447 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 283 449 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 284 451 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 285 452 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 286 454 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 287 455 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 288 457 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 289 459 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 290 460 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 291 462 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 292 463 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 293 465 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 294 466 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 295 468 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 296 470 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 297 471 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 298 473 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 299 474 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 300 476 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 301 478 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 302 479 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 303 481 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 304 482 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 305 484 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd
  · exact close_case 306 485 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2) hd

end Collatz.FiniteCases
