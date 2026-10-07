import X2Y5Z7.FiniteFields.Basic
import X2Y5Z7.Fields.FrobeniusBridge

/-! # Irreducibility of the model polynomials (Rabin's criterion)

`irreducible_of_rabin`: over a finite field `K` with `Q` elements, a monic `p` of degree `n > 0` is irreducible if
`p ∣ X^(Q^n) - X`, and for a list `es` covering the proper divisors of `n` (every `d ∣ n` with `d < n` divides some
`e ∈ es`), `X^(Q^e) - X` is invertible modulo `p`. Proof: an irreducible factor `g` has degree `d ∣ n`; if `d < n`
then `g ∣ X^(Q^e) - X` for some `e ∈ es` (`X2Y5Z7.dvd_X_pow_card_pow_sub_X_of_natDegree_dvd`), so `g ∣ 1`.

`irrCheck q P cert` checks the hypotheses by computation in `AdjoinRoot (toPoly q P)` (`cert` lists pairs `(e, W)`
with `W = (X^(q^e) - X)⁻¹ mod P`), and `irreducible_of_irrCheck` concludes `Irreducible (toPoly q P)`. -/

namespace X2Y5Z7.FiniteFields

open Polynomial

theorem irreducible_of_rabin {K : Type*} [Field K] [Fintype K] {p : K[X]} (hm : p.Monic) (hd : 0 < p.natDegree)
    (hfrob : p ∣ X ^ (Fintype.card K) ^ p.natDegree - X) (es : List ℕ)
    (hcov : ∀ d, 0 < d → d < p.natDegree → d ∣ p.natDegree → ∃ e ∈ es, d ∣ e)
    (hcop : ∀ e ∈ es, ∃ w : K[X], p ∣ (X ^ (Fintype.card K) ^ e - X) * w - 1) : Irreducible p := by
  have hp0 : p ≠ 0 := hm.ne_zero
  have hpu : ¬ IsUnit p := fun hu => by
    have := natDegree_eq_zero_of_isUnit hu; omega
  obtain ⟨g, hg, hgp⟩ := WfDvdMonoid.exists_irreducible_factor hpu hp0
  have hdvd : g.natDegree ∣ p.natDegree := by
    apply hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    rw [Nat.card_eq_fintype_card]; exact hgp.trans hfrob
  have hle : g.natDegree ≤ p.natDegree := Nat.le_of_dvd hd hdvd
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨e, he, hde⟩ := hcov _ hg.natDegree_pos hlt hdvd
    obtain ⟨w, hw⟩ := hcop e he
    have h1 : g ∣ X ^ (Fintype.card K) ^ e - X := dvd_X_pow_card_pow_sub_X_of_natDegree_dvd hg hde
    have h2 : g ∣ 1 := by
      have := dvd_sub (dvd_mul_of_dvd_left h1 w) (hgp.trans hw)
      rwa [sub_sub_cancel] at this
    exact hg.not_isUnit (isUnit_of_dvd_one h2)
  · exact (associated_of_dvd_of_natDegree_le hgp hp0 heq.ge).irreducible hg

/-- Every proper divisor `d` of `f` divides some `e ∈ es`. -/
def coverOK (f : ℕ) (es : List ℕ) : Bool :=
  (List.range f).all (fun d => d == 0 || f % d != 0 || es.any (fun e => e % d == 0))

/-- The computational Rabin test for `toPoly q P`, with inverse certificates `(e, W)`. -/
def irrCheck (q : ℕ) (P : List ℕ) (cert : List (ℕ × List ℕ)) : Bool :=
  validP P && coverOK (P.length - 1) (cert.map Prod.fst) &&
    eqL q (ruleOf q P) (powL q (ruleOf q P) [0, 1] (q ^ (P.length - 1))) [0, 1] &&
    cert.all (fun c => eqL q (ruleOf q P)
      (mulL q (ruleOf q P) (subL q (powL q (ruleOf q P) [0, 1] (q ^ c.1)) [0, 1]) (reduceL q (ruleOf q P) c.2)) [1])

theorem ev_X (q : ℕ) (P : List ℕ) : ev q P [0, 1] = AdjoinRoot.root (toPoly q P) := by simp [ev]

theorem irreducible_of_irrCheck {q : ℕ} [hq : Fact q.Prime] {P : List ℕ} {cert : List (ℕ × List ℕ)}
    (h : irrCheck q P cert = true) : Irreducible (toPoly q P) := by
  simp only [irrCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hv, hcov⟩, hfrob⟩, hcert⟩ := h
  have hq0 : 0 < q := hq.out.pos
  have hM := isModel_root hq0 hv
  obtain ⟨hmon, hdeg⟩ := toPoly_monic (q := q) hv
  have hlen : P.length - 1 = P.dropLast.length := by simp
  have hf := (eq_of_validP hv).2
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  refine irreducible_of_rabin hmon (by omega) ?_ (cert.map Prod.fst) ?_ ?_
  · rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, hcard, hdeg, ← hlen, ← ev_X,
      ← ev_powL hq0 hv, ev_eq_of_eqL hq0 hv _ _ hfrob, sub_self]
  · intro d hd0 hdf hdd
    simp only [coverOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq, List.any_eq_true] at hcov
    rcases hcov d (by omega) with (h0 | h1) | ⟨e, he, hde⟩
    · omega
    · exact absurd (Nat.mod_eq_zero_of_dvd (show d ∣ P.length - 1 by rw [hlen, ← hdeg]; exact hdd)) h1
    · exact ⟨e, he, Nat.dvd_of_mod_eq_zero (by simpa using hde)⟩
  · intro e he
    obtain ⟨⟨e', W⟩, hmem, rfl⟩ := List.mem_map.mp he
    refine ⟨toPoly q W, ?_⟩
    have h1 := ev_eq_of_eqL hq0 hv _ _ (hcert _ hmem)
    have e1 : ev q P (reduceL q (ruleOf q P) W) = ev q P W := evL_reduceL hM W
    have e2 : ∀ A B, ev q P (subL q A B) = ev q P A - ev q P B := fun A B => evL_subL hM.qpos hM.char A B
    rw [ev_mulL hq0 hv _ _ (by rw [← length_ruleOf q P]; exact length_reduceL hM.fpos _), e2, e1,
      ev_powL hq0 hv, ev_X, ev_const] at h1
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, map_sub, map_pow, AdjoinRoot.mk_X, hcard, map_one,
      ← ev_eq_mk, h1, Nat.cast_one, sub_self]

end X2Y5Z7.FiniteFields
