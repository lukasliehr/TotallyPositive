import LeanCode.Vendor.E5.P11.Part11.Basic
import LeanCode.Vendor.E5.Defs
















theorem one_transport (R : ℝ → ℝ) (hfe : ∀ x : ℝ, R (x + 1) = (R x)⁻¹)
    (x : ℝ) (hx : R x = 1) : R (x + 1) = 1 := by
  rw [hfe, hx, inv_one]







theorem recip_high (R : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < R x)
    (hfe : ∀ x : ℝ, R (x + 1) = (R x)⁻¹) (w : ℝ) (hw : R w < 1) :
    1 < R (w + 1) := by
  rw [hfe]
  exact one_lt_inv_iff₀.mpr ⟨hpos w, hw⟩









theorem high (R : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < R x)
    (hfe : ∀ x : ℝ, R (x + 1) = (R x)⁻¹)
    (hne : ∀ u v : ℝ, u < v → ∃ x : ℝ, u < x ∧ x < v ∧ R x ≠ 1)
    (u v : ℝ) (huv : u < v) :
    ∃ z : ℝ, ((u < z ∧ z < v) ∨ (u + 1 < z ∧ z < v + 1)) ∧ 1 < R z := by
  obtain ⟨w, huw, hwv, hwne⟩ := hne u v huv
  rcases lt_or_gt_of_ne hwne with hlt | hgt
  · exact ⟨w + 1, Or.inr ⟨by linarith, by linarith⟩, recip_high R hpos hfe w hlt⟩
  · exact ⟨w, Or.inl ⟨huw, hwv⟩, hgt⟩








theorem const (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    1 < (1 + min a b) / 2 ∧ (1 + min a b) / 2 < a ∧
      (1 + min a b) / 2 < b ∧ 0 < (1 + min a b) / 2 := by
  have hm : 1 < min a b := lt_min_iff.mpr ⟨ha, hb⟩
  have hma : min a b ≤ a := min_le_left a b
  have hmb : min a b ≤ b := min_le_right a b
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩









theorem four (F : ℝ → ℝ) (r s : ℝ) (_hrs : r < s) (_hsr1 : s < r + 1)
    (hFs : F s < 0) (hFr1 : F (r + 1) < 0) (hFs1 : F (s + 1) < 0)
    (hFr2 : F (r + 2) < 0)
    (hz0 : ∃ z₀ : ℝ, ((r < z₀ ∧ z₀ < s) ∨ (r + 1 < z₀ ∧ z₀ < s + 1)) ∧ 0 < F z₀)
    (hz1 : ∃ z₁ : ℝ, ((s < z₁ ∧ z₁ < r + 1) ∨ (s + 1 < z₁ ∧ z₁ < r + 2)) ∧ 0 < F z₁) :
    CyclicAlt4 F := by
  obtain ⟨z₀, hz0loc, hz0pos⟩ := hz0
  obtain ⟨z₁, hz1loc, hz1pos⟩ := hz1
  rcases hz0loc with ⟨hz0a, hz0b⟩ | ⟨hz0a, hz0b⟩ <;>
    rcases hz1loc with ⟨hz1a, hz1b⟩ | ⟨hz1a, hz1b⟩
  ·
    exact witness F z₀ s z₁ (r + 1) hz0b hz1a hz1b (by linarith)
      hz0pos hFs hz1pos hFr1
  ·
    exact witness F z₀ (r + 1) z₁ (r + 2) (by linarith) (by linarith) hz1b (by linarith)
      hz0pos hFr1 hz1pos hFr2
  ·
    exact witness F z₁ (r + 1) z₀ (s + 1) hz1b hz0a hz0b (by linarith)
      hz1pos hFr1 hz0pos hFs1
  ·
    exact witness F z₀ (s + 1) z₁ (r + 2) hz0b hz1a hz1b (by linarith)
      hz0pos hFs1 hz1pos hFr2












theorem core (R : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < R x)
    (hfe : ∀ x : ℝ, R (x + 1) = (R x)⁻¹)
    (hcyc : ∀ c : ℝ, 0 < c → ¬ CyclicAlt4 (fun x => R x - c))
    (hne : ∀ u v : ℝ, u < v → ∃ x : ℝ, u < x ∧ x < v ∧ R x ≠ 1) :
    ¬ ∃ r s : ℝ, 0 ≤ r ∧ r < s ∧ s < 1 ∧ R r = 1 ∧ R s = 1 := by
  rintro ⟨r, s, hr0, hrs, hs1, hRr, hRs⟩

  have hRr1 : R (r + 1) = 1 := one_transport R hfe r hRr
  have hRr2 : R (r + 2) = 1 := by
    have h := one_transport R hfe (r + 1) hRr1
    have e : r + 1 + 1 = r + 2 := by ring
    rwa [e] at h
  have hRs1 : R (s + 1) = 1 := one_transport R hfe s hRs

  have hsr1 : s < r + 1 := by linarith

  obtain ⟨z₀, hz0loc, hz0high⟩ := high R hpos hfe hne r s hrs
  obtain ⟨z₁, hz1loc, hz1high⟩ := high R hpos hfe hne s (r + 1) hsr1

  obtain ⟨hc1, hcz0, hcz1, hc0⟩ := const (R z₀) (R z₁) hz0high hz1high
  set c : ℝ := (1 + min (R z₀) (R z₁)) / 2

  refine hcyc c hc0 ?_
  apply four (fun x => R x - c) r s hrs hsr1
  · show R s - c < 0; rw [hRs]; linarith
  · show R (r + 1) - c < 0; rw [hRr1]; linarith
  · show R (s + 1) - c < 0; rw [hRs1]; linarith
  · show R (r + 2) - c < 0; rw [hRr2]; linarith
  · refine ⟨z₀, ?_, by show 0 < R z₀ - c; linarith⟩
    rcases hz0loc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · refine ⟨z₁, ?_, by show 0 < R z₁ - c; linarith⟩
    rcases hz1loc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
