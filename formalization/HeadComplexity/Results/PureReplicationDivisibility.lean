import HeadComplexity.Results.PureSecondReplicationDegree
import HeadComplexity.Polynomial.ReplicatedInputCopy
import HeadComplexity.Results.HeadBudgetPullback

/-!
# Replication divisibility and the even replicated source

Copying each bit a positive number of times preserves every centered group
mean. Consequently threshold degree is monotone along divisibility of the
replication count. The two-replica quadratic obstruction therefore proves
threshold degree and pure rotary minimum exactly three at every positive
even replication. No vanilla three-head upper bound is asserted here.
-/

namespace HeadComplexity.PureThreeReplicatedGrid

open ThresholdDegreePullback

theorem coordinate_replication_copy {m k : ℕ} (hk : 0 < k)
    (x : Fin (18 * m) → Bool) :
    coordinate (m := m * k) (x ∘ ReplicatedInputCopy.projection 18 m k) =
      coordinate x :=
  ReplicatedInputCopy.coordinate_copy hk x

theorem classifier_replication_copy {m k : ℕ} (hk : 0 < k)
    (x : Fin (18 * m) → Bool) :
    classifier (m * k) (x ∘ ReplicatedInputCopy.projection 18 m k) = classifier m x := by
  unfold classifier
  rw [coordinate_replication_copy hk]

theorem pure_computable_of_replication_multiple {m k H : ℕ} (hk : 0 < k)
    (hf : pureRoPEComputable (18 * (m * k)) H (classifier (m * k))) :
    pureRoPEComputable (18 * m) H (classifier m) := by
  have h := CoordinateIdentification.pure_pullback
    (ReplicatedInputCopy.projection 18 m k) (ReplicatedInputCopy.projection_surjective hk) hf
  simpa only [classifier_replication_copy hk] using h

theorem vanilla_computable_of_replication_multiple {m k H : ℕ} (hk : 0 < k)
    (hf : computableWithSharedHeadsN (18 * (m * k)) H (classifier (m * k))) :
    computableWithSharedHeadsN (18 * m) H (classifier m) := by
  have h := CoordinateIdentification.vanilla_pullback
    (ReplicatedInputCopy.projection 18 m k) (ReplicatedInputCopy.projection_surjective hk) hf
  simpa only [classifier_replication_copy hk] using h

theorem pure_head_minimum_replication_mul_le {m k : ℕ} (hk : 0 < k) :
    PureRoPEHStar (18 * m) (classifier m) ≤
      PureRoPEHStar (18 * (m * k)) (classifier (m * k)) := by
  have h := CoordinateIdentification.pure_minimum_pullback_le
    (ReplicatedInputCopy.projection 18 m k) (ReplicatedInputCopy.projection_surjective hk)
    (classifier (m * k))
  simpa only [classifier_replication_copy hk] using h

theorem vanilla_head_minimum_replication_mul_le {m k : ℕ} (hk : 0 < k) :
    HStar (18 * m) (classifier m) ≤ HStar (18 * (m * k)) (classifier (m * k)) := by
  have h := CoordinateIdentification.original_minimum_pullback_le
    (ReplicatedInputCopy.projection 18 m k) (ReplicatedInputCopy.projection_surjective hk)
    (classifier (m * k))
  simpa only [classifier_replication_copy hk] using h

theorem head_minima_replication_dvd_le {m M : ℕ} (hM : 0 < M) (hdiv : m ∣ M) :
    PureRoPEHStar (18 * m) (classifier m) ≤ PureRoPEHStar (18 * M) (classifier M) ∧
      StandardPureRoPEHStar (18 * m) (classifier m) ≤
        StandardPureRoPEHStar (18 * M) (classifier M) ∧
      FreePureRoPEHStar (18 * m) (classifier m) ≤
        FreePureRoPEHStar (18 * M) (classifier M) ∧
      SharedHStar (18 * m) (classifier m) ≤ SharedHStar (18 * M) (classifier M) ∧
      HStar (18 * m) (classifier m) ≤ HStar (18 * M) (classifier M) := by
  obtain ⟨k, rfl⟩ := hdiv
  have hk : 0 < k := by nlinarith
  rw [standardPureRoPEHStar_eq_scalar, standardPureRoPEHStar_eq_scalar,
    freePureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar,
    SharedHStar_eq_HStar, SharedHStar_eq_HStar]
  exact ⟨pure_head_minimum_replication_mul_le hk,
    pure_head_minimum_replication_mul_le hk, pure_head_minimum_replication_mul_le hk,
    vanilla_head_minimum_replication_mul_le hk, vanilla_head_minimum_replication_mul_le hk⟩

theorem thresholdDegLE_of_replication_multiple {m k d : ℕ} (hk : 0 < k)
    (hf : ThresholdDegLE (classifier (m * k)) d) :
    ThresholdDegLE (classifier m) d := by
  have h := thresholdDegLE_pullback (ReplicatedInputCopy.projection 18 m k) _ hf
  simpa only [classifier_replication_copy hk] using h

theorem thresholdDeg_replication_mul_le {m k : ℕ} (hk : 0 < k) :
    thresholdDeg (classifier m) ≤ thresholdDeg (classifier (m * k)) :=
  thresholdDeg_le_of_witness _
    (thresholdDegLE_of_replication_multiple hk (thresholdDegLE_minimum _))

theorem thresholdDeg_replication_dvd_le {m M : ℕ} (hM : 0 < M) (hdiv : m ∣ M) :
    thresholdDeg (classifier m) ≤ thresholdDeg (classifier M) := by
  obtain ⟨k, rfl⟩ := hdiv
  have hk : 0 < k := by nlinarith
  exact thresholdDeg_replication_mul_le hk

theorem classifier_even_not_thresholdDegLE_two {k : ℕ} (hk : 0 < k) :
    ¬ ThresholdDegLE (classifier (2 * k)) 2 := by
  intro h
  exact classifier_two_not_thresholdDegLE_two
    (thresholdDegLE_of_replication_multiple hk h)

theorem classifier_even_threshold_degree {k : ℕ} (hk : 0 < k) :
    thresholdDeg (classifier (2 * k)) = 3 := by
  have hl := thresholdDeg_replication_mul_le (m := 2) hk
  rw [classifier_two_threshold_degree] at hl
  have hu := thresholdDeg_le_of_witness _
    (thresholdDegLE_of_pureRoPEComputable (pure_computable (2 * k) (by omega)))
  omega

theorem classifier_even_pure_head_minimum {k : ℕ} (hk : 0 < k) :
    PureRoPEHStar (18 * (2 * k)) (classifier (2 * k)) = 3 := by
  classical
  have hu : PureRoPEHStar (18 * (2 * k)) (classifier (2 * k)) ≤ 3 :=
    Nat.find_min' (exists_pureRoPEComputable _) (pure_computable (2 * k) (by omega))
  have hl : 3 ≤ PureRoPEHStar (18 * (2 * k)) (classifier (2 * k)) := by
    have h := thresholdDeg_le_of_witness _
      (thresholdDegLE_of_pureRoPEComputable (pureRoPEHStar_computable (classifier (2 * k))))
    rwa [classifier_even_threshold_degree hk] at h
  omega

theorem classifier_even_head_minima {k : ℕ} (hk : 0 < k) :
    PureRoPEHStar (18 * (2 * k)) (classifier (2 * k)) = 3 ∧
      StandardPureRoPEHStar (18 * (2 * k)) (classifier (2 * k)) = 3 ∧
      FreePureRoPEHStar (18 * (2 * k)) (classifier (2 * k)) = 3 ∧
      3 ≤ SharedHStar (18 * (2 * k)) (classifier (2 * k)) := by
  have hp := classifier_even_pure_head_minimum hk
  rw [standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar,
    SharedHStar_eq_HStar]
  refine ⟨hp, hp, hp, ?_⟩
  have hl := pureRoPEHStar_le_vanilla (classifier (2 * k))
  change PureRoPEHStar (18 * (2 * k)) (classifier (2 * k)) ≤
    HStar (18 * (2 * k)) (classifier (2 * k)) at hl
  omega

end HeadComplexity.PureThreeReplicatedGrid
