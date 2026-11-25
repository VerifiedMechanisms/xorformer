import HeadComplexity.Results.PureGeneralReplicatedGrid
import HeadComplexity.Results.HeadBudgetPullback
import HeadComplexity.Polynomial.ReplicatedInputCopy
import HeadComplexity.Results.RoPEArchitecturalComparison

/-!
# Divisibility monotonicity for every source head count

This is an exact finite-input statement, independent of the eventual
separation theorem. Replication divisibility preserves centered group means
under coordinate identification. Threshold degree and all the established
minimum-head APIs are therefore monotone along positive multiples.
-/

namespace HeadComplexity.PureGeneralReplicatedGrid

theorem coordinate_replication_copy {H m k : ℕ} (hk : 0 < k)
    (x : Fin (groupCount H * m) → Bool) :
    coordinate (H := H) (m := m * k)
      (x ∘ ReplicatedInputCopy.projection (groupCount H) m k) = coordinate x :=
  ReplicatedInputCopy.coordinate_copy hk x

theorem classifier_replication_copy {H m k : ℕ} (hk : 0 < k)
    (x : Fin (groupCount H * m) → Bool) :
    classifier H (m * k) (x ∘ ReplicatedInputCopy.projection (groupCount H) m k) =
      classifier H m x := by
  unfold classifier
  rw [coordinate_replication_copy hk]

theorem pure_computable_of_replication_multiple {H m k h : ℕ} (hk : 0 < k)
    (hf : pureRoPEComputable (groupCount H * (m * k)) h (classifier H (m * k))) :
    pureRoPEComputable (groupCount H * m) h (classifier H m) := by
  have h := CoordinateIdentification.pure_pullback
    (ReplicatedInputCopy.projection (groupCount H) m k)
    (ReplicatedInputCopy.projection_surjective hk) hf
  simpa only [classifier_replication_copy hk] using h

theorem vanilla_computable_of_replication_multiple {H m k h : ℕ} (hk : 0 < k)
    (hf : computableWithHeadsN (groupCount H * (m * k)) h (classifier H (m * k))) :
    computableWithHeadsN (groupCount H * m) h (classifier H m) := by
  have h := CoordinateIdentification.original_vanilla_pullback
    (ReplicatedInputCopy.projection (groupCount H) m k)
    (ReplicatedInputCopy.projection_surjective hk) hf
  simpa only [classifier_replication_copy hk] using h

theorem thresholdDeg_replication_mul_le {H m k : ℕ} (hk : 0 < k) :
    thresholdDeg (classifier H m) ≤ thresholdDeg (classifier H (m * k)) := by
  have h := ThresholdDegreePullback.thresholdDeg_pullback_le
    (ReplicatedInputCopy.projection (groupCount H) m k) (classifier H (m * k))
  simpa only [classifier_replication_copy hk] using h

theorem pure_head_minimum_replication_mul_le {H m k : ℕ} (hk : 0 < k) :
    PureRoPEHStar (groupCount H * m) (classifier H m) ≤
      PureRoPEHStar (groupCount H * (m * k)) (classifier H (m * k)) := by
  have h := CoordinateIdentification.pure_minimum_pullback_le
    (ReplicatedInputCopy.projection (groupCount H) m k)
    (ReplicatedInputCopy.projection_surjective hk) (classifier H (m * k))
  simpa only [classifier_replication_copy hk] using h

theorem vanilla_head_minimum_replication_mul_le {H m k : ℕ} (hk : 0 < k) :
    HStar (groupCount H * m) (classifier H m) ≤
      HStar (groupCount H * (m * k)) (classifier H (m * k)) := by
  have h := CoordinateIdentification.original_minimum_pullback_le
    (ReplicatedInputCopy.projection (groupCount H) m k)
    (ReplicatedInputCopy.projection_surjective hk) (classifier H (m * k))
  simpa only [classifier_replication_copy hk] using h

theorem complexities_replication_dvd_le {H m M : ℕ} (hM : 0 < M) (hdiv : m ∣ M) :
    thresholdDeg (classifier H m) ≤ thresholdDeg (classifier H M) ∧
      PureRoPEHStar (groupCount H * m) (classifier H m) ≤
        PureRoPEHStar (groupCount H * M) (classifier H M) ∧
      StandardPureRoPEHStar (groupCount H * m) (classifier H m) ≤
        StandardPureRoPEHStar (groupCount H * M) (classifier H M) ∧
      FreePureRoPEHStar (groupCount H * m) (classifier H m) ≤
        FreePureRoPEHStar (groupCount H * M) (classifier H M) ∧
      SharedHStar (groupCount H * m) (classifier H m) ≤
        SharedHStar (groupCount H * M) (classifier H M) ∧
      HStar (groupCount H * m) (classifier H m) ≤
        HStar (groupCount H * M) (classifier H M) := by
  obtain ⟨k, rfl⟩ := hdiv
  have hk : 0 < k := by nlinarith
  rw [standardPureRoPEHStar_eq_scalar, standardPureRoPEHStar_eq_scalar,
    freePureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar,
    SharedHStar_eq_HStar, SharedHStar_eq_HStar]
  exact ⟨thresholdDeg_replication_mul_le hk, pure_head_minimum_replication_mul_le hk,
    pure_head_minimum_replication_mul_le hk, pure_head_minimum_replication_mul_le hk,
    vanilla_head_minimum_replication_mul_le hk, vanilla_head_minimum_replication_mul_le hk⟩

end HeadComplexity.PureGeneralReplicatedGrid
