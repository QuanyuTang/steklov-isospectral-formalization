module

public import Mathlib

/-!
# Transplantation kernels from monodromy-invariant matrices

Let `p₁ : E₁ → X`, `p₂ : E₂ → X` be covering maps over a path-connected base `X`, with fibres over
a base point `x₀` labelled by `L₁, L₂`, and let `T` be a matrix such that
`T (L₁ (mon₁ γ a)) (L₂ (mon₂ γ b)) = T (L₁ a) (L₂ b)` for every loop `γ` at `x₀` (`IsInvariant`).
Parallel transport of `T` along paths to `x₀` defines a kernel `K e₁ e₂` on the fibre product
`{(e₁, e₂) | p₁ e₁ = p₂ e₂}` (`kernel`) which is

* independent of the chosen path (`fibK_eq`) and invariant under transport (`fibK_transport`);
* **locally constant on the fibre product** if `X` is locally path connected
  (`kernel_eventually_eq`);
* fibrewise orthonormal when `T` has orthonormal columns/rows and the labels are bijections
  (`fibK_sum_mul`, `fibK_sum_mul'`).

All of this is unconditional covering-space theory (Mathlib's path-lifting monodromy).
-/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace CoverKernel

/-! ### Local lifts in an evenly covered neighbourhood -/

/-- Near a point `e` of a covering, every path in a small neighbourhood of `p e` that ends at
`p e` and starts at the image of a point `e'` in a small neighbourhood of `e` lifts from `e'` to
`e`. -/
theorem exists_local_lift {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] {p : E → X}
    (cov : IsCoveringMap p) (e : E) :
    ∃ V : Set X, IsOpen V ∧ p e ∈ V ∧ ∃ N ∈ 𝓝 e, ∀ e' ∈ N, ∀ γ : Path (p e') (p e),
      (∀ s, γ s ∈ V) → cov.monodromy (Path.Homotopic.Quotient.mk γ) ⟨e', rfl⟩ = ⟨e, rfl⟩ := by
  haveI : Nonempty (p ⁻¹' {p e}) := ⟨⟨e, rfl⟩⟩
  have hev := cov (p e)
  haveI := hev.discreteTopology_fiber
  set t := hev.toTrivialization with ht
  have hbase : p e ∈ t.baseSet := hev.mem_toTrivialization_baseSet
  have hsrc : e ∈ t.source := by rw [t.mem_source]; exact hbase
  refine ⟨t.baseSet, t.open_baseSet, hbase, t.source ∩ (fun e' => (t e').2) ⁻¹' {(t e).2}, ?_, ?_⟩
  · refine (ContinuousOn.isOpen_inter_preimage (continuous_snd.comp_continuousOn
      t.continuousOn_toFun) t.open_source (isOpen_discrete _)).mem_nhds ⟨hsrc, rfl⟩
  rintro e' ⟨he's, he'⟩ γ hγ
  -- the explicit lift
  set Γ : C(unitInterval, E) := ⟨fun s => t.toOpenPartialHomeomorph.symm (γ s, (t e).2), by
    refine t.continuousOn_invFun.comp_continuous (by fun_prop) fun s => ?_
    rw [t.target_eq]; exact ⟨hγ s, mem_univ _⟩⟩ with hΓ
  have hlift : Γ = cov.liftPath (γ : C(unitInterval, X)) e' (γ.source.trans rfl) := by
    rw [cov.eq_liftPath_iff']
    refine ⟨funext fun s => ?_, ?_⟩
    · exact t.proj_symm_apply' (hγ s)
    · show t.toOpenPartialHomeomorph.symm (γ 0, (t e).2) = e'
      rw [γ.source]
      have h1 : (t e').2 = (t e).2 := he'
      rw [← h1]
      exact t.symm_apply_mk_proj he's
  apply Subtype.ext
  show cov.liftPath (γ : C(unitInterval, X)) e' _ 1 = e
  rw [← hlift]
  show t.toOpenPartialHomeomorph.symm (γ 1, (t e).2) = e
  rw [γ.target]
  exact t.symm_apply_mk_proj hsrc

/-! ### The transported kernel -/

variable {X E₁ E₂ : Type*} [TopologicalSpace X] [TopologicalSpace E₁] [TopologicalSpace E₂]
  {p₁ : E₁ → X} {p₂ : E₂ → X} (cov₁ : IsCoveringMap p₁) (cov₂ : IsCoveringMap p₂)
  [PathConnectedSpace X] (x₀ : X) {ι κ : Type*} (L₁ : p₁ ⁻¹' {x₀} → ι) (L₂ : p₂ ⁻¹' {x₀} → κ)
  (T : ι → κ → ℝ)

/-- A chosen homotopy class of paths from `x` to the base point. -/
def toBase (x : X) : Path.Homotopic.Quotient x x₀ :=
  Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x₀)

/-- The kernel on the fibres over `x`, obtained by transporting both points to `x₀`. -/
def fibK (x : X) (a : p₁ ⁻¹' {x}) (b : p₂ ⁻¹' {x}) : ℝ :=
  T (L₁ (cov₁.monodromy (toBase x₀ x) a)) (L₂ (cov₂.monodromy (toBase x₀ x) b))

/-- Monodromy invariance of `T`. -/
def IsInvariant : Prop :=
  ∀ (γ : Path.Homotopic.Quotient x₀ x₀) (a : p₁ ⁻¹' {x₀}) (b : p₂ ⁻¹' {x₀}),
    T (L₁ (cov₁.monodromy γ a)) (L₂ (cov₂.monodromy γ b)) = T (L₁ a) (L₂ b)

variable {cov₁ cov₂ x₀ L₁ L₂ T}

omit [PathConnectedSpace X] in
lemma monodromy_symm_apply {E : Type*} [TopologicalSpace E] {p : E → X} (cov : IsCoveringMap p)
    {x y : X} (δ : Path.Homotopic.Quotient x y) (a : p ⁻¹' {x}) :
    cov.monodromy δ.symm (cov.monodromy δ a) = a := by
  rw [← cov.monodromy_trans_apply, Path.Homotopic.Quotient.trans_symm, cov.monodromy_refl]; rfl

/-- **Path independence.** -/
theorem fibK_eq (hT : IsInvariant cov₁ cov₂ x₀ L₁ L₂ T) {x : X}
    (η : Path.Homotopic.Quotient x x₀) (a : p₁ ⁻¹' {x}) (b : p₂ ⁻¹' {x}) :
    fibK cov₁ cov₂ x₀ L₁ L₂ T x a b =
      T (L₁ (cov₁.monodromy η a)) (L₂ (cov₂.monodromy η b)) := by
  set δ := toBase x₀ x
  have key1 : cov₁.monodromy η a = cov₁.monodromy (δ.symm.trans η) (cov₁.monodromy δ a) := by
    rw [cov₁.monodromy_trans_apply, monodromy_symm_apply]
  have key2 : cov₂.monodromy η b = cov₂.monodromy (δ.symm.trans η) (cov₂.monodromy δ b) := by
    rw [cov₂.monodromy_trans_apply, monodromy_symm_apply]
  rw [key1, key2, hT]
  rfl

/-- **Transport invariance**: the kernel is unchanged under parallel transport along any path. -/
theorem fibK_transport (hT : IsInvariant cov₁ cov₂ x₀ L₁ L₂ T) {x y : X}
    (β : Path.Homotopic.Quotient x y) (a : p₁ ⁻¹' {x}) (b : p₂ ⁻¹' {x}) :
    fibK cov₁ cov₂ x₀ L₁ L₂ T y (cov₁.monodromy β a) (cov₂.monodromy β b) =
      fibK cov₁ cov₂ x₀ L₁ L₂ T x a b := by
  rw [fibK_eq hT (β.trans (toBase x₀ y)), cov₁.monodromy_trans_apply,
    cov₂.monodromy_trans_apply]
  rfl

open Classical in
variable (cov₁ cov₂ x₀ L₁ L₂ T) in
/-- The kernel on `E₁ × E₂`, supported on the fibre product. -/
def kernel (e₁ : E₁) (e₂ : E₂) : ℝ :=
  if h : p₂ e₂ = p₁ e₁ then fibK cov₁ cov₂ x₀ L₁ L₂ T (p₁ e₁) ⟨e₁, rfl⟩ ⟨e₂, h⟩ else 0

lemma kernel_of_eq {e₁ : E₁} {e₂ : E₂} (h : p₂ e₂ = p₁ e₁) :
    kernel cov₁ cov₂ x₀ L₁ L₂ T e₁ e₂ = fibK cov₁ cov₂ x₀ L₁ L₂ T (p₁ e₁) ⟨e₁, rfl⟩ ⟨e₂, h⟩ :=
  dif_pos h

/-- The kernel expressed on any fibre. -/
lemma kernel_fibre {x : X} (a : p₁ ⁻¹' {x}) (b : p₂ ⁻¹' {x}) :
    kernel cov₁ cov₂ x₀ L₁ L₂ T a b = fibK cov₁ cov₂ x₀ L₁ L₂ T x a b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have ha' : p₁ a = x := ha
  have hb' : p₂ b = x := hb
  subst ha'
  exact kernel_of_eq hb'

/-- **Local constancy on the fibre product.** -/
theorem kernel_eventually_eq [LocallyPathConnectedSpace X] (hT : IsInvariant cov₁ cov₂ x₀ L₁ L₂ T)
    {e₁ : E₁} {e₂ : E₂} (h : p₂ e₂ = p₁ e₁) :
    ∀ᶠ q in 𝓝 (e₁, e₂), p₂ q.2 = p₁ q.1 →
      kernel cov₁ cov₂ x₀ L₁ L₂ T q.1 q.2 = kernel cov₁ cov₂ x₀ L₁ L₂ T e₁ e₂ := by
  obtain ⟨V₁, hV₁o, hV₁, N₁, hN₁, hlift₁⟩ := exists_local_lift cov₁ e₁
  obtain ⟨V₂, hV₂o, hV₂, N₂, hN₂, hlift₂⟩ := exists_local_lift cov₂ e₂
  rw [h] at hV₂
  -- a path-connected neighbourhood of `p₁ e₁` inside `V₁ ∩ V₂`
  obtain ⟨W, ⟨hWn, hWpc⟩, hWV⟩ := (path_connected_basis (p₁ e₁)).mem_iff.1
    (inter_mem (hV₁o.mem_nhds hV₁) (hV₂o.mem_nhds hV₂))
  have hc : ContinuousAt p₁ e₁ := cov₁.continuous.continuousAt
  have hev : ∀ᶠ q : E₁ × E₂ in 𝓝 (e₁, e₂), q.1 ∈ N₁ ∧ q.2 ∈ N₂ ∧ p₁ q.1 ∈ W := by
    have h1 : ∀ᶠ q : E₁ × E₂ in 𝓝 (e₁, e₂), q.1 ∈ N₁ := continuous_fst.continuousAt hN₁
    have h2 : ∀ᶠ q : E₁ × E₂ in 𝓝 (e₁, e₂), q.2 ∈ N₂ := continuous_snd.continuousAt hN₂
    have h3 : ∀ᶠ q : E₁ × E₂ in 𝓝 (e₁, e₂), p₁ q.1 ∈ W :=
      (hc.comp continuous_fst.continuousAt) hWn
    filter_upwards [h1, h2, h3] with q a b c using ⟨a, b, c⟩
  filter_upwards [hev] with q ⟨hq1, hq2, hqW⟩ hq
  obtain ⟨γ, hγW⟩ := hWpc.joinedIn _ hqW _ (mem_of_mem_nhds hWn)
  have hγ1 := hlift₁ q.1 hq1 γ fun s => (hWV (hγW s)).1
  set γ₂ : Path (p₂ q.2) (p₂ e₂) := γ.cast hq h
  have hγ2 := hlift₂ q.2 hq2 γ₂ fun s => (hWV (hγW s)).2
  rw [kernel_of_eq hq, kernel_of_eq h, ← fibK_transport hT (Path.Homotopic.Quotient.mk γ), hγ1]
  congr 1
  apply Subtype.ext
  have := congrArg Subtype.val hγ2
  exact this

/-! ### Orthonormality -/

open Classical in
/-- **Fibrewise orthonormality** (sum over the first cover). -/
theorem fibK_sum_mul [Fintype ι] {x : X} [Fintype (p₁ ⁻¹' {x})] (hL₁ : Function.Bijective L₁)
    (hL₂ : Function.Injective L₂) (hcol : ∀ j j', ∑ i, T i j * T i j' = if j = j' then 1 else 0)
    (b b' : p₂ ⁻¹' {x}) :
    ∑ a : p₁ ⁻¹' {x}, fibK cov₁ cov₂ x₀ L₁ L₂ T x a b * fibK cov₁ cov₂ x₀ L₁ L₂ T x a b' =
      if b = b' then 1 else 0 := by
  classical
  set δ := toBase x₀ x
  have hbij : Function.Bijective fun a : p₁ ⁻¹' {x} => L₁ (cov₁.monodromy δ a) :=
    hL₁.comp (cov₁.monodromy_bijective δ)
  have hinj : Function.Injective fun b : p₂ ⁻¹' {x} => L₂ (cov₂.monodromy δ b) :=
    hL₂.comp (cov₂.monodromy_bijective δ).1
  unfold fibK
  rw [Function.Bijective.sum_comp hbij (fun i => T i (L₂ (cov₂.monodromy δ b)) *
    T i (L₂ (cov₂.monodromy δ b'))), hcol]
  exact if_congr hinj.eq_iff rfl rfl

open Classical in
/-- **Fibrewise orthonormality** (sum over the second cover). -/
theorem fibK_sum_mul' [Fintype κ] {x : X} [Fintype (p₂ ⁻¹' {x})] (hL₁ : Function.Injective L₁)
    (hL₂ : Function.Bijective L₂) (hrow : ∀ i i', ∑ j, T i j * T i' j = if i = i' then 1 else 0)
    (a a' : p₁ ⁻¹' {x}) :
    ∑ b : p₂ ⁻¹' {x}, fibK cov₁ cov₂ x₀ L₁ L₂ T x a b * fibK cov₁ cov₂ x₀ L₁ L₂ T x a' b =
      if a = a' then 1 else 0 := by
  classical
  set δ := toBase x₀ x
  have hbij : Function.Bijective fun b : p₂ ⁻¹' {x} => L₂ (cov₂.monodromy δ b) :=
    hL₂.comp (cov₂.monodromy_bijective δ)
  have hinj : Function.Injective fun a : p₁ ⁻¹' {x} => L₁ (cov₁.monodromy δ a) :=
    hL₁.comp (cov₁.monodromy_bijective δ).1
  unfold fibK
  rw [Function.Bijective.sum_comp hbij (fun j => T (L₁ (cov₁.monodromy δ a)) j *
    T (L₁ (cov₁.monodromy δ a')) j), hrow]
  exact if_congr hinj.eq_iff rfl rfl

/-- The kernel is bounded by the entries of `T`. -/
theorem abs_kernel_le [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] (e₁ : E₁) (e₂ : E₂) :
    |kernel cov₁ cov₂ x₀ L₁ L₂ T e₁ e₂| ≤
      Finset.univ.sup' Finset.univ_nonempty fun ij : ι × κ => |T ij.1 ij.2| := by
  unfold kernel
  split_ifs
  · exact Finset.le_sup' (fun ij : ι × κ => |T ij.1 ij.2|) (Finset.mem_univ (_, _))
  · rw [abs_zero]
    exact (abs_nonneg _).trans
      (Finset.le_sup' (fun ij : ι × κ => |T ij.1 ij.2|) (Finset.mem_univ (Classical.arbitrary _)))

end CoverKernel
