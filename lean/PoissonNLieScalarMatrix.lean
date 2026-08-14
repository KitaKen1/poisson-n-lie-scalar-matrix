import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The scalar-matrix Poisson n-Lie conjecture

This file reproduces the exact definitions and target theorem from
Formal Conjectures PR #4893, without depending on or cloning the FC repository.
-/

namespace Arxiv.«2605.01785»

variable {F : Type*} [Field F]
variable {A : Type*} [CommRing A] [Algebra F A]
variable {n m : ℕ}

noncomputable def bracketMatrix
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x : Fin n → A) : Matrix (Fin (n + m)) (Fin (n + m)) A :=
  Matrix.of fun i j =>
    if h : j.val < n
    then d i (x ⟨j.val, h⟩)
    else algebraMap F A (M i ⟨j.val - n, by omega⟩)

noncomputable def nLieBracket
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x : Fin n → A) : A :=
  Matrix.det (bracketMatrix d M x)

def FilippovIdentity (b : (Fin n → A) → A) : Prop :=
  ∀ (x : Fin n → A) (y : Fin n → A) (k : Fin n),
    b (Function.update x k (b y)) =
      ∑ i : Fin n,
        b (Function.update y i (b (Function.update x k (y i))))

def LeibnizRule (b : (Fin n → A) → A) : Prop :=
  ∀ (x : Fin n → A) (k : Fin n) (a c : A),
    b (Function.update x k (a * c)) =
      b (Function.update x k a) * c + a * b (Function.update x k c)

def Alternating (b : (Fin n → A) → A) : Prop :=
  ∀ (x : Fin n → A) (i j : Fin n), i ≠ j →
    b (x ∘ Equiv.swap i j) = -(b x)

def IsPoissonNLie (b : (Fin n → A) → A) : Prop :=
  Alternating b ∧ FilippovIdentity b ∧ LeibnizRule b

/-! ## The square Jacobian core -/

noncomputable def jacobianMatrix
    (d : Fin n → Derivation F A A) (x : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  fun i j => d i (x j)

noncomputable def jacobianBracket
    (d : Fin n → Derivation F A A) (x : Fin n → A) : A :=
  (jacobianMatrix d x).det

lemma jacobianMatrix_update
    (d : Fin n → Derivation F A A) (x : Fin n → A) (k : Fin n) (a : A) :
    jacobianMatrix d (Function.update x k a) =
      (jacobianMatrix d x).updateCol k (fun i => d i a) := by
  classical
  ext i j
  by_cases h : j = k
  · subst j
    simp [jacobianMatrix]
  · simp [jacobianMatrix, h]

lemma jacobianBracket_alternating (d : Fin n → Derivation F A A) :
    Alternating (jacobianBracket d) := by
  classical
  intro x i j hij
  simp only [jacobianBracket]
  have hmatrix :
      jacobianMatrix d (x ∘ Equiv.swap i j) =
        (jacobianMatrix d x).submatrix id (Equiv.swap i j) := by
    ext r c
    rfl
  rw [hmatrix, Matrix.det_permute', Equiv.Perm.sign_swap hij]
  simp

lemma jacobianBracket_leibniz (d : Fin n → Derivation F A A) :
    LeibnizRule (jacobianBracket d) := by
  classical
  intro x k a c
  simp only [jacobianBracket, jacobianMatrix_update]
  have hcol : (fun i => d i (a * c)) =
      a • (fun i => d i c) + c • (fun i => d i a) := by
    funext i
    simp [Derivation.leibniz, smul_eq_mul]
  rw [hcol, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
    Matrix.det_updateCol_smul]
  ring

lemma sum_det_updateCol_mul (C Y : Matrix (Fin n) (Fin n) A) :
    (∑ i : Fin n, (Y.updateCol i (fun r => (C * Y) r i)).det) =
      C.trace * Y.det := by
  classical
  calc
    (∑ i : Fin n, (Y.updateCol i (fun r => (C * Y) r i)).det) =
        (Y.adjugate * (C * Y)).trace := by
          simp only [Matrix.trace, Matrix.diag]
          apply Finset.sum_congr rfl
          intro i _
          rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
          simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    _ = (Y * Y.adjugate * C).trace := by
          rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    _ = C.trace * Y.det := by
          rw [Matrix.mul_adjugate]
          simp [Matrix.trace_smul, mul_comm]

lemma derivation_finset_prod {ι : Type*} [DecidableEq ι]
    (D : Derivation F A A) (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) =
      ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha,
        Finset.erase_insert ha]
      simp only [smul_eq_mul]
      have hrest :
          (∑ i ∈ s, D (f i) * ∏ j ∈ (insert a s).erase i, f j) =
            f a * ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hai : a ≠ i := fun h => ha (h ▸ hi)
        rw [Finset.erase_insert_of_ne hai, Finset.prod_insert]
        · ring
        · exact fun h => ha (Finset.mem_of_mem_erase h)
      rw [hrest]
      ring

lemma derivation_det (D : Derivation F A A) (Y : Matrix (Fin n) (Fin n) A) :
    D Y.det =
      ∑ j : Fin n, (Y.updateCol j (fun i => D (Y i j))).det := by
  classical
  rw [Matrix.det_apply', map_sum]
  simp_rw [D.leibniz, D.map_intCast, smul_eq_mul, mul_zero, add_zero,
    derivation_finset_prod D Finset.univ, Finset.mul_sum]
  simp_rw [Matrix.det_apply']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have hfun :
      (fun i => (Y.updateCol j (fun r => D (Y r j))) (σ i) i) =
        Function.update (fun i => Y (σ i) i) j (D (Y (σ j) j)) := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [h]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j),
    Finset.sdiff_singleton_eq_erase]

lemma det_updateCol_eq_sum_basis (Y : Matrix (Fin n) (Fin n) A)
    (j : Fin n) (v : Fin n → A) :
    (Y.updateCol j v).det =
      ∑ r : Fin n, v r * (Y.updateCol j (Pi.single r (1 : A))).det := by
  classical
  change Matrix.cramer Y v j = _
  calc
    Matrix.cramer Y v j = Matrix.cramer Y
        (∑ r : Fin n, v r • (Pi.single r (1 : A) : Fin n → A)) j := by
      rw [← pi_eq_sum_univ' v]
    _ = ∑ r : Fin n,
        Matrix.cramer Y (v r • (Pi.single r (1 : A) : Fin n → A)) j := by
      rw [map_sum]
      simp only [Finset.sum_apply]
    _ = _ := by
      simp only [Matrix.cramer_apply, Matrix.det_updateCol_smul]

lemma det_updateCol_sum_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : Matrix (Fin n) (Fin n) A) (j : Fin n)
    (c : ι → A) (v : ι → Fin n → A) :
    (Y.updateCol j (∑ r : ι, c r • v r)).det =
      ∑ r : ι, c r * (Y.updateCol j (v r)).det := by
  classical
  change Matrix.cramer Y (∑ r : ι, c r • v r) j = _
  rw [map_sum]
  simp only [Finset.sum_apply, Matrix.cramer_apply, Matrix.det_updateCol_smul]

lemma det_two_basisCols_self (Y : Matrix (Fin n) (Fin n) A)
    {k j : Fin n} (hkj : k ≠ j) (r : Fin n) :
    ((Y.updateCol k (Pi.single r 1)).updateCol j (Pi.single r 1)).det = 0 := by
  classical
  apply Matrix.det_zero_of_column_eq hkj
  intro i
  simp [hkj]

lemma det_two_basisCols_swap (Y : Matrix (Fin n) (Fin n) A)
    {k j : Fin n} (hkj : k ≠ j) (r s : Fin n) :
    ((Y.updateCol k (Pi.single s 1)).updateCol j (Pi.single r 1)).det =
      -((Y.updateCol k (Pi.single r 1)).updateCol j (Pi.single s 1)).det := by
  classical
  let Z := (Y.updateCol k (Pi.single r 1)).updateCol j (Pi.single s 1)
  have hmatrix :
      (Y.updateCol k (Pi.single s 1)).updateCol j (Pi.single r 1) =
        Z.submatrix id (Equiv.swap k j) := by
    ext i c
    by_cases hck : c = k
    · subst c
      simp [Z, hkj]
    · by_cases hcj : c = j
      · subst c
        simp [Z, hkj]
      · simp [Z, hck, hcj,
          Equiv.swap_apply_of_ne_of_ne hck hcj]
  rw [hmatrix, Matrix.det_permute', Equiv.Perm.sign_swap hkj]
  simp [Z]

lemma sum_symmetric_mul_skew
    (H Z : Fin n → Fin n → A)
    (hsym : ∀ r s, H r s = H s r)
    (hdiag : ∀ r, Z r r = 0)
    (hskew : ∀ r s, Z s r = -Z r s) :
    (∑ r : Fin n, ∑ s : Fin n, H r s * Z r s) = 0 := by
  classical
  rw [← Finset.sum_product' Finset.univ Finset.univ]
  apply Finset.sum_involution (fun p _ => (p.2, p.1))
  · rintro ⟨r, s⟩ hp
    simp only
    rw [hsym r s, hskew r s]
    ring
  · rintro ⟨r, s⟩ hp hrs hpair
    have hsr : s = r := by simpa using congrArg Prod.fst hpair
    subst s
    exact hrs (by simp [hdiag])
  · rintro ⟨r, s⟩ hp
    simp
  · rintro ⟨r, s⟩ hp
    simp

lemma adjugate_apply_eq_det_updateCol_single
    (Y : Matrix (Fin n) (Fin n) A) (k r : Fin n) :
    Y.adjugate k r = (Y.updateCol k (Pi.single r 1)).det := by
  classical
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

lemma derivation_bracketMatrix_apply
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F) (x : Fin n → A)
    (r i j : Fin (n + m)) :
    d r (bracketMatrix d M x i j) =
      if h : j.val < n then d r (d i (x ⟨j.val, h⟩)) else 0 := by
  classical
  simp only [bracketMatrix, Matrix.of_apply]
  split_ifs with h
  · rfl
  · simp

lemma bracketMatrix_update
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x : Fin n → A) (k : Fin n) (a : A) :
    bracketMatrix d M (Function.update x k a) =
      (bracketMatrix d M x).updateCol (Fin.castAdd m k) (fun i => d i a) := by
  classical
  ext i j
  by_cases hjk : j = Fin.castAdd m k
  · subst j
    simp [bracketMatrix]
  · by_cases hj : j.val < n
    · have hfin : (⟨j.val, hj⟩ : Fin n) ≠ k := by
        intro h
        apply hjk
        apply Fin.ext
        simpa using congrArg Fin.val h
      simp [bracketMatrix, hjk, hj, hfin]
    · simp [bracketMatrix, hjk, hj]

lemma swap_castAdd (i j c : Fin n) :
    Equiv.swap (Fin.castAdd m i) (Fin.castAdd m j) (Fin.castAdd m c) =
      Fin.castAdd m (Equiv.swap i j c) := by
  classical
  by_cases hci : c = i
  · subst c
    simp
  · by_cases hcj : c = j
    · subst c
      simp
    · have hci' : Fin.castAdd m c ≠ Fin.castAdd m i := by
        intro h
        apply hci
        apply Fin.ext
        simpa using congrArg Fin.val h
      have hcj' : Fin.castAdd m c ≠ Fin.castAdd m j := by
        intro h
        apply hcj
        apply Fin.ext
        simpa using congrArg Fin.val h
      simp [Equiv.swap_apply_of_ne_of_ne hci hcj,
        Equiv.swap_apply_of_ne_of_ne hci' hcj']

lemma nLieBracket_alternating
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F) :
    Alternating (nLieBracket d M) := by
  classical
  intro x i j hij
  let i' : Fin (n + m) := Fin.castAdd m i
  let j' : Fin (n + m) := Fin.castAdd m j
  have hi'j' : i' ≠ j' := by
    intro h
    apply hij
    apply Fin.ext
    simpa [i', j'] using congrArg Fin.val h
  have hmatrix :
      bracketMatrix d M (x ∘ Equiv.swap i j) =
        (bracketMatrix d M x).submatrix id (Equiv.swap i' j') := by
    ext r c
    by_cases hc : c.val < n
    · let c₀ : Fin n := ⟨c.val, hc⟩
      have hcc₀ : c = Fin.castAdd m c₀ := by rfl
      rw [hcc₀]
      simp only [bracketMatrix, Matrix.of_apply, Matrix.submatrix_apply,
        Function.comp_apply]
      rw [show Equiv.swap i' j' (Fin.castAdd m c₀) =
          Fin.castAdd m (Equiv.swap i j c₀) by
        simpa [i', j'] using swap_castAdd (m := m) i j c₀]
      simp
    · have hci : c ≠ i' := by
        intro h
        apply hc
        have hval : c.val = i.val := by simpa [i'] using congrArg Fin.val h
        omega
      have hcj : c ≠ j' := by
        intro h
        apply hc
        have hval : c.val = j.val := by simpa [j'] using congrArg Fin.val h
        omega
      simp [bracketMatrix, hc, Equiv.swap_apply_of_ne_of_ne hci hcj]
  simp only [nLieBracket]
  rw [hmatrix, Matrix.det_permute', Equiv.Perm.sign_swap hi'j']
  simp

lemma nLieBracket_leibniz
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F) :
    LeibnizRule (nLieBracket d M) := by
  classical
  intro x k a c
  simp only [nLieBracket, bracketMatrix_update]
  have hcol : (fun i => d i (a * c)) =
      a • (fun i => d i c) + c • (fun i => d i a) := by
    funext i
    simp [Derivation.leibniz, smul_eq_mul]
  rw [hcol, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
    Matrix.det_updateCol_smul]
  ring

lemma nLieBracket_update_eq_sum_adjugate
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x : Fin n → A) (k : Fin n) (a : A) :
    nLieBracket d M (Function.update x k a) =
      ∑ r : Fin (n + m),
        (bracketMatrix d M x).adjugate (Fin.castAdd m k) r * d r a := by
  classical
  simp only [nLieBracket, bracketMatrix_update]
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp [Matrix.mulVec, dotProduct]

lemma derivation_nLieBracket
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x : Fin n → A) (r : Fin (n + m)) :
    d r (nLieBracket d M x) =
      ∑ i : Fin n,
        ((bracketMatrix d M x).updateCol (Fin.castAdd m i)
          (fun s => d r (d s (x i)))).det := by
  classical
  let Y := bracketMatrix d M x
  let T : Fin (n + m) → A := fun j =>
    (Y.updateCol j (fun s => d r (Y s j))).det
  have hdet : d r (nLieBracket d M x) = ∑ j : Fin (n + m), T j := by
    simp only [nLieBracket, T, Y]
    exact derivation_det _ _
  rw [hdet]
  calc
    (∑ j : Fin (n + m), T j) =
        ∑ q : Fin n ⊕ Fin m, T (finSumFinEquiv q) := by
      symm
      exact finSumFinEquiv.sum_comp T
    _ = (∑ i : Fin n, T (Fin.castAdd m i)) +
        ∑ q : Fin m, T (Fin.natAdd n q) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = ∑ i : Fin n, T (Fin.castAdd m i) := by
      rw [add_eq_left]
      apply Finset.sum_eq_zero
      intro q hq
      apply Matrix.det_eq_zero_of_column_eq_zero (Fin.natAdd n q)
      intro s
      simp [Y, derivation_bracketMatrix_apply]
    _ = ∑ i : Fin n,
        (Y.updateCol (Fin.castAdd m i) (fun s => d r (d s (x i)))).det := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [T]
      congr 1
      funext s
      simp [Y, derivation_bracketMatrix_apply]
    _ = _ := rfl

lemma cofactor_derivative_mul_const
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x y : Fin n → A) (k : Fin n) (s : Fin (n + m)) (q : Fin m) :
    (∑ r : Fin (n + m),
      d s ((bracketMatrix d M x).adjugate (Fin.castAdd m k) r) *
        bracketMatrix d M y r (Fin.natAdd n q)) = 0 := by
  classical
  let X := bracketMatrix d M x
  let Y := bracketMatrix d M y
  let k' : Fin (n + m) := Fin.castAdd m k
  let j : Fin (n + m) := Fin.natAdd n q
  have hkj : k' ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    simp [k', j] at hval
    omega
  have horth : (∑ r : Fin (n + m), X.adjugate k' r * X r j) = 0 := by
    have h := congrArg (fun Z : Matrix (Fin (n + m)) (Fin (n + m)) A => Z k' j)
      (Matrix.adjugate_mul X)
    simpa [Matrix.mul_apply, Matrix.one_apply, hkj] using h
  have hd := congrArg (d s) horth
  simp only [map_sum] at hd
  simp_rw [(d s).leibniz] at hd
  change (∑ r : Fin (n + m), d s (X.adjugate k' r) * Y r j) = 0
  simpa [X, Y, j, derivation_bracketMatrix_apply, bracketMatrix, mul_comm] using hd

lemma bracketMatrix_piola
    (d : Fin (n + m) → Derivation F A A)
    (hcomm : ∀ i j : Fin (n + m), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (n + m)) (Fin m) F) (x : Fin n → A) (k : Fin n) :
    (∑ r : Fin (n + m),
      d r ((bracketMatrix d M x).adjugate (Fin.castAdd m k) r)) = 0 := by
  classical
  let Y := bracketMatrix d M x
  let k' : Fin (n + m) := Fin.castAdd m k
  change (∑ r : Fin (n + m), d r (Y.adjugate k' r)) = 0
  simp_rw [adjugate_apply_eq_det_updateCol_single]
  simp_rw [derivation_det]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hjmem
  by_cases hjk : j = k'
  · subst j
    apply Finset.sum_eq_zero
    intro r hrmem
    apply Matrix.det_eq_zero_of_column_eq_zero k'
    intro i
    by_cases hir : i = r
    · subst i
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hir]
  · by_cases hj : j.val < n
    · have hk'j : k' ≠ j := Ne.symm hjk
      have hcol : ∀ r : Fin (n + m),
          (fun i => d r ((Y.updateCol k' (Pi.single r 1)) i j)) =
            fun i => d r (d i (x ⟨j.val, hj⟩)) := by
        intro r
        funext i
        simp [Y, k', hjk, derivation_bracketMatrix_apply, hj]
      simp_rw [hcol]
      calc
        (∑ r : Fin (n + m),
            ((Y.updateCol k' (Pi.single r 1)).updateCol j
              (fun i => d r (d i (x ⟨j.val, hj⟩)))).det) =
            ∑ r : Fin (n + m), ∑ s : Fin (n + m),
              d r (d s (x ⟨j.val, hj⟩)) *
                ((Y.updateCol k' (Pi.single r 1)).updateCol j
                  (Pi.single s 1)).det := by
          apply Finset.sum_congr rfl
          intro r hrmem
          exact det_updateCol_eq_sum_basis _ _ _
        _ = 0 := by
          apply sum_symmetric_mul_skew
          · intro r s
            exact hcomm r s _
          · intro r
            exact det_two_basisCols_self Y hk'j r
          · intro r s
            exact det_two_basisCols_swap Y hk'j r s
    · apply Finset.sum_eq_zero
      intro r hrmem
      apply Matrix.det_eq_zero_of_column_eq_zero j
      intro i
      simp [Y, k', hjk, derivation_bracketMatrix_apply, hj]

lemma cofactor_trace_det_sum_zero
    (d : Fin (n + m) → Derivation F A A)
    (hcomm : ∀ i j : Fin (n + m), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x y : Fin n → A) (k : Fin n) :
    (∑ i : Fin n,
      ((bracketMatrix d M y).updateCol (Fin.castAdd m i) (fun s =>
        ∑ r : Fin (n + m),
          d s ((bracketMatrix d M x).adjugate (Fin.castAdd m k) r) *
            bracketMatrix d M y r (Fin.castAdd m i))).det) = 0 := by
  classical
  let X := bracketMatrix d M x
  let Y := bracketMatrix d M y
  let k' : Fin (n + m) := Fin.castAdd m k
  let C : Matrix (Fin (n + m)) (Fin (n + m)) A :=
    fun s r => d s (X.adjugate k' r)
  change (∑ i : Fin n,
    (Y.updateCol (Fin.castAdd m i) (fun s => (C * Y) s (Fin.castAdd m i))).det) = 0
  have htrace : C.trace = 0 := by
    simpa [C, Matrix.trace, Matrix.diag, X, k'] using
      bracketMatrix_piola d hcomm M x k
  have hconst : ∀ q : Fin m, ∀ s : Fin (n + m),
      (C * Y) s (Fin.natAdd n q) = 0 := by
    intro q s
    simp only [Matrix.mul_apply, C, Y, X, k']
    exact cofactor_derivative_mul_const d M x y k s q
  have hall :
      (∑ j : Fin (n + m),
        (Y.updateCol j (fun s => (C * Y) s j)).det) =
        ∑ i : Fin n,
          (Y.updateCol (Fin.castAdd m i)
            (fun s => (C * Y) s (Fin.castAdd m i))).det := by
    calc
      (∑ j : Fin (n + m),
          (Y.updateCol j (fun s => (C * Y) s j)).det) =
          ∑ q : Fin n ⊕ Fin m,
            (Y.updateCol (finSumFinEquiv q)
              (fun s => (C * Y) s (finSumFinEquiv q))).det := by
        symm
        exact (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).sum_comp
          (fun j => (Y.updateCol j (fun s => (C * Y) s j)).det)
      _ = (∑ i : Fin n,
            (Y.updateCol (Fin.castAdd m i)
              (fun s => (C * Y) s (Fin.castAdd m i))).det) +
          ∑ q : Fin m,
            (Y.updateCol (Fin.natAdd n q)
              (fun s => (C * Y) s (Fin.natAdd n q))).det := by
        rw [Fintype.sum_sum_type]
        rfl
      _ = _ := by
        rw [add_eq_left]
        apply Finset.sum_eq_zero
        intro q hq
        apply Matrix.det_eq_zero_of_column_eq_zero (Fin.natAdd n q)
        intro s
        simp [hconst q s]
  rw [← hall, sum_det_updateCol_mul, htrace, zero_mul]

lemma nLieBracket_filippov
    (d : Fin (n + m) → Derivation F A A)
    (hcomm : ∀ i j : Fin (n + m), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (n + m)) (Fin m) F) :
    FilippovIdentity (nLieBracket d M) := by
  classical
  intro x y k
  let X := bracketMatrix d M x
  let Y := bracketMatrix d M y
  let k' : Fin (n + m) := Fin.castAdd m k
  let c : Fin (n + m) → A := fun r => X.adjugate k' r
  let U : Fin n → Fin (n + m) → A := fun i s =>
    ∑ r : Fin (n + m), d s (c r) * d r (y i)
  let V : Fin n → Fin (n + m) → A := fun i s =>
    ∑ r : Fin (n + m), c r * d r (d s (y i))
  have hUpdate (a : A) :
      nLieBracket d M (Function.update x k a) =
        ∑ r : Fin (n + m), c r * d r a := by
    simpa [c, X, k'] using nLieBracket_update_eq_sum_adjugate d M x k a
  have hder (i : Fin n) :
      (fun s => d s (nLieBracket d M (Function.update x k (y i)))) =
        U i + V i := by
    rw [hUpdate (y i)]
    funext s
    simp only [map_sum]
    simp_rw [(d s).leibniz, hcomm s]
    rw [Finset.sum_add_distrib]
    simp [U, V, mul_comm, add_comm]
  have hOuter (i : Fin n) (a : A) :
      nLieBracket d M (Function.update y i a) =
        (Y.updateCol (Fin.castAdd m i) (fun s => d s a)).det := by
    simp [nLieBracket, bracketMatrix_update, Y]
  have hfirst :
      (∑ i : Fin n, (Y.updateCol (Fin.castAdd m i) (U i)).det) = 0 := by
    simpa [U, c, X, Y, k', bracketMatrix] using
      cofactor_trace_det_sum_zero d hcomm M x y k
  have hleft :
      nLieBracket d M (Function.update x k (nLieBracket d M y)) =
        ∑ i : Fin n, (Y.updateCol (Fin.castAdd m i) (V i)).det := by
    rw [hUpdate (nLieBracket d M y)]
    simp_rw [derivation_nLieBracket]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hV : V i =
        ∑ r : Fin (n + m), c r • (fun s => d r (d s (y i))) := by
      funext s
      simp [V]
    rw [hV, det_updateCol_sum_smul]
  have hright :
      (∑ i : Fin n,
        nLieBracket d M
          (Function.update y i
            (nLieBracket d M (Function.update x k (y i))))) =
        (∑ i : Fin n, (Y.updateCol (Fin.castAdd m i) (U i)).det) +
          ∑ i : Fin n, (Y.updateCol (Fin.castAdd m i) (V i)).det := by
    simp_rw [hOuter]
    simp_rw [hder, Matrix.det_updateCol_add]
    exact Finset.sum_add_distrib
  rw [hleft, hright, hfirst, zero_add]

/-!
The unrestricted theorem is stated first.  The final declaration then keeps the
exact name and type used by PR #4893 and is an immediate corollary.
-/

theorem poissonNLie_of_scalarMatrix_general (n m : ℕ)
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Algebra F A]
    (d : Fin (n + m) → Derivation F A A)
    (hcomm : ∀ i j : Fin (n + m), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (n + m)) (Fin m) F) :
    IsPoissonNLie (nLieBracket d M) := by
  exact ⟨nLieBracket_alternating d M, nLieBracket_filippov d hcomm M,
    nLieBracket_leibniz d M⟩

set_option linter.unusedVariables false in
theorem poissonNLie_of_scalarMatrix (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm : 1 ≤ m)
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Algebra F A]
    (d : Fin (n + m) → Derivation F A A)
    (hcomm : ∀ i j : Fin (n + m), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (n + m)) (Fin m) F) :
    IsPoissonNLie (nLieBracket d M) := by
  exact poissonNLie_of_scalarMatrix_general n m d hcomm M

end Arxiv.«2605.01785»

/-! ## Kernel audit: unrestricted theorem first, exact FC target second -/

#check Arxiv.«2605.01785».poissonNLie_of_scalarMatrix_general
#print axioms Arxiv.«2605.01785».poissonNLie_of_scalarMatrix_general

#check Arxiv.«2605.01785».poissonNLie_of_scalarMatrix
#print axioms Arxiv.«2605.01785».poissonNLie_of_scalarMatrix
