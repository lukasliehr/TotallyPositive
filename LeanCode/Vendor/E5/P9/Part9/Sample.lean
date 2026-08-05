import LeanCode.Vendor.E5.P9.Part9.Defs
import LeanCode.Vendor.E5.Defs












noncomputable def sample (u : Fin 4 → ℝ) (M : ℕ) : Fin (4 * (2 * M + 1)) → ℝ :=
  fun i => u ⟨(i : ℕ) % 4, by omega⟩ + (2 * (((i : ℕ) / 4 : ℕ) : ℝ) - 2 * (M : ℝ))


theorem lem_signstab {a b η : ℝ} (hη : 0 < η) (hab : |a - b| < η) (ha : 2 * η ≤ |a|)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hpos : 0 < σ * a) : 0 < σ * b := by
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  have hsa : σ * a = |a| := by
    have h := abs_mul σ a
    rw [hσabs, one_mul] at h
    rw [← h, abs_of_pos hpos]
  have habs2 : |σ * (a - b)| = |a - b| := by rw [abs_mul, hσabs, one_mul]
  have h1 : σ * (a - b) ≤ |a - b| := by rw [← habs2]; exact le_abs_self _
  have goaleq : σ * b = σ * a - σ * (a - b) := by ring
  linarith


theorem lem_transfer {m : ℕ} (x : Fin m → ℝ) (F G : ℝ → ℝ) {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (ha : ∀ i : Fin m, 0 < ε * (-1 : ℝ) ^ (i : ℕ) * F (x i))
    (hb : ∀ i : Fin m, 2 * η ≤ |F (x i)|)
    (hc : ∀ i : Fin m, |F (x i) - G (x i)| < η) :
    ∀ i : Fin m, 0 < ε * (-1 : ℝ) ^ (i : ℕ) * G (x i) := by
  intro i
  have hpm : (-1 : ℝ) ^ (i : ℕ) = 1 ∨ (-1 : ℝ) ^ (i : ℕ) = -1 := by
    rcases Nat.even_or_odd (i : ℕ) with he | ho
    · exact Or.inl (Even.neg_one_pow he)
    · exact Or.inr (Odd.neg_one_pow ho)
  have hσ : ε * (-1 : ℝ) ^ (i : ℕ) = 1 ∨ ε * (-1 : ℝ) ^ (i : ℕ) = -1 := by
    rcases hε with h | h <;> rcases hpm with h2 | h2 <;> rw [h, h2] <;> norm_num
  exact lem_signstab hη (hc i) (hb i) hσ (ha i)



theorem lem_altvec {s : ℕ} (v : Fin (s + 1) → ℝ)
    (h : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ i : Fin (s + 1), 0 < ε * (-1 : ℝ) ^ (i : ℕ) * v i) :
    SignChangesGE v s := by
  obtain ⟨ε, hε, hv⟩ := h
  exact ⟨id, strictMono_id, ε, hε, hv⟩


theorem lem_samplemono {u : Fin 4 → ℝ} (hu : StrictMono u) (hu2 : u 3 < u 0 + 2) (M : ℕ) :
    StrictMono (sample u M) := by
  intro i j hij
  have hlt : (i : ℕ) < (j : ℕ) := hij
  show u ⟨(i : ℕ) % 4, by omega⟩ + (2 * (((i : ℕ) / 4 : ℕ) : ℝ) - 2 * (M : ℝ))
     < u ⟨(j : ℕ) % 4, by omega⟩ + (2 * (((j : ℕ) / 4 : ℕ) : ℝ) - 2 * (M : ℝ))
  rcases Nat.lt_or_ge ((i : ℕ) / 4) ((j : ℕ) / 4) with hdlt | hdge
  · have hui : u ⟨(i : ℕ) % 4, by omega⟩ ≤ u 3 := hu.monotone (by omega)
    have huj : u 0 ≤ u ⟨(j : ℕ) % 4, by omega⟩ := hu.monotone (by omega)
    have hgap : (((i : ℕ) / 4 : ℕ) : ℝ) + 1 ≤ (((j : ℕ) / 4 : ℕ) : ℝ) := by
      have h : (i : ℕ) / 4 + 1 ≤ (j : ℕ) / 4 := hdlt
      exact_mod_cast h
    linarith
  · have hdeq : (i : ℕ) / 4 = (j : ℕ) / 4 := by omega
    have hdeqR : (((i : ℕ) / 4 : ℕ) : ℝ) = (((j : ℕ) / 4 : ℕ) : ℝ) := by exact_mod_cast hdeq
    have hmodlt : (i : ℕ) % 4 < (j : ℕ) % 4 := by omega
    have hustep : u ⟨(i : ℕ) % 4, by omega⟩ < u ⟨(j : ℕ) % 4, by omega⟩ := hu (by omega)
    linarith



theorem lem_samplesign {F : ℝ → ℝ} (hper : ∀ (x : ℝ) (k : ℤ), F (x + 2 * (k : ℝ)) = F x)
    {u : Fin 4 → ℝ} (hu : StrictMono u) (M : ℕ)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hsign : ∀ j : Fin 4, 0 < ε * (-1 : ℝ) ^ (j : ℕ) * F (u j)) :
    ∀ i : Fin (4 * (2 * M + 1)),
      F (sample u M i) = F (u ⟨(i : ℕ) % 4, by omega⟩)
        ∧ 0 < ε * (-1 : ℝ) ^ (i : ℕ) * F (sample u M i) := by
  intro i
  have hper_i : F (sample u M i) = F (u ⟨(i : ℕ) % 4, by omega⟩) := by
    show F (u ⟨(i : ℕ) % 4, by omega⟩ + (2 * (((i : ℕ) / 4 : ℕ) : ℝ) - 2 * (M : ℝ)))
        = F (u ⟨(i : ℕ) % 4, by omega⟩)
    have hk : (2 * (((i : ℕ) / 4 : ℕ) : ℝ) - 2 * (M : ℝ))
            = 2 * (((((i : ℕ) / 4 : ℕ) : ℤ) - (M : ℤ) : ℤ) : ℝ) := by
      simp only [Int.cast_sub, Int.cast_natCast]; ring
    rw [hk]
    exact hper (u ⟨(i : ℕ) % 4, by omega⟩) ((((i : ℕ) / 4 : ℕ) : ℤ) - (M : ℤ))
  refine ⟨hper_i, ?_⟩
  rw [hper_i]
  have hpar : (-1 : ℝ) ^ (i : ℕ) = (-1 : ℝ) ^ ((i : ℕ) % 4) := by
    conv_lhs => rw [← Nat.div_add_mod (i : ℕ) 4]
    rw [pow_add, pow_mul]; norm_num
  rw [hpar]
  exact hsign ⟨(i : ℕ) % 4, by omega⟩



theorem lem_samplerange {u : Fin 4 → ℝ} (hu : StrictMono u) (M : ℕ) {K : ℝ}
    (hK : max |u 0| |u 3| ≤ K) :
    ∀ i : Fin (4 * (2 * M + 1)), |sample u M i| ≤ K + 2 * (M : ℝ) := by
  intro i
  have hi : (i : ℕ) < 4 * (2 * M + 1) := i.isLt
  have hu0 : u 0 ≤ u ⟨(i : ℕ) % 4, by omega⟩ := hu.monotone (by omega)
  have hu3 : u ⟨(i : ℕ) % 4, by omega⟩ ≤ u 3 := hu.monotone (by omega)
  have hur : |u ⟨(i : ℕ) % 4, by omega⟩| ≤ max |u 0| |u 3| := abs_le_max_abs_abs hu0 hu3
  have hq2 : (((i : ℕ) / 4 : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
    have h : (i : ℕ) / 4 ≤ 2 * M := by omega
    exact_mod_cast h
  have hq0 : (0 : ℝ) ≤ (((i : ℕ) / 4 : ℕ) : ℝ) := by positivity
  have habs : |2 * (((i : ℕ) / 4 : ℕ) : ℝ) - 2 * (M : ℝ)| ≤ 2 * (M : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  show |u ⟨(i : ℕ) % 4, by omega⟩ + (2 * (((i : ℕ) / 4 : ℕ) : ℝ) - 2 * (M : ℝ))| ≤ K + 2 * (M : ℝ)
  calc |u ⟨(i : ℕ) % 4, by omega⟩ + (2 * (((i : ℕ) / 4 : ℕ) : ℝ) - 2 * (M : ℝ))|
      ≤ |u ⟨(i : ℕ) % 4, by omega⟩| + |2 * (((i : ℕ) / 4 : ℕ) : ℝ) - 2 * (M : ℝ)| := abs_add_le _ _
    _ ≤ max |u 0| |u 3| + 2 * (M : ℝ) := add_le_add hur habs
    _ ≤ K + 2 * (M : ℝ) := by linarith
