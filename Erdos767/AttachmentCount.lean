import Erdos767.AttachmentPaths

namespace Erdos767
open SimpleGraph
universe u
noncomputable section
set_option maxHeartbeats 800000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : SimpleGraph V} [DecidableRel K.Adj]

/-- Every component outside a cycle in a 2-connected graph has at least
two distinct attachment vertices on the cycle. -/
theorem two_le_componentAttachmentCount
    (C : CycleWitness K) (h2c : IsTwoConnected K)
    (c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    2 ≤ componentAttachmentCount C c := by
  classical
  let Q := componentOutsideFinset C c
  let T := setNeighborsIn K Q C.vertexFinset
  have hQ := componentOutsideFinset_isComponent C c
  change 2 ≤ T.card
  by_contra hsmall
  have hcard : T.card ≤ 1 := by omega
  obtain ⟨a, haC, hTsub⟩ :
      ∃ a : V, a ∈ C.vertexFinset ∧ T ⊆ {a} := by
    by_cases hT : T.Nonempty
    · let a := hT.choose
      have haT : a ∈ T := hT.choose_spec
      have haC : a ∈ C.vertexFinset := (Finset.mem_filter.mp haT).1
      refine ⟨a, haC, ?_⟩
      intro t ht
      simp only [Finset.mem_singleton]
      by_contra hta
      have hpair : ({a, t} : Finset V) ⊆ T := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact haT
        · exact ht
      have htwo : 2 ≤ T.card := by
        have hpCard : ({a, t} : Finset V).card = 2 := by
          have hat : a ≠ t := Ne.symm hta
          simp [hat]
        rw [← hpCard]
        exact Finset.card_le_card hpair
      omega
    · refine ⟨C.base, C.base_mem_vertexFinset, ?_⟩
      intro t ht
      exact (hT ⟨t, ht⟩).elim
  have hcycleCard : 1 < C.vertexFinset.card := by
    rw [C.card_vertexFinset]
    exact lt_of_lt_of_le (by decide : 1 < 3) C.isCycle.three_le_length
  obtain ⟨w, hwC, hwa⟩ := C.vertexFinset.exists_mem_ne hcycleCard a
  obtain ⟨z, hzQ⟩ := hQ.1
  have hzNotA : z ≠ a := by
    intro hza
    subst z
    exact (Finset.mem_sdiff.mp (hQ.2.1 hzQ)).2 haC
  let zz : ↥(({a} : Set V)ᶜ) := ⟨z, by simp [hzNotA]⟩
  let ww : ↥(({a} : Set V)ᶜ) := ⟨w, by simp [hwa]⟩
  obtain ⟨p⟩ := (h2c.2 a).preconnected zz ww
  have walk_stays_in_Q :
      ∀ {u v : ↥(({a} : Set V)ᶜ)}
        (r : (K.induce (({a} : Set V)ᶜ)).Walk u v),
        (u : V) ∈ Q → (v : V) ∈ Q := by
    intro u v r
    induction r with
    | nil => intro hu; exact hu
    | @cons u v w huv r ih =>
        intro huQ
        have hvQ : (v : V) ∈ Q := by
          by_cases hvC : (v : V) ∈ C.vertexFinset
          · have hvT : (v : V) ∈ T := by
              apply Finset.mem_filter.mpr
              exact ⟨hvC, (u : V), huQ, huv.symm⟩
            have hva : (v : V) = a := by
              simpa using hTsub hvT
            have hvNotA : (v : V) ≠ a := by
              have hv := v.property
              change (v : V) ∉ ({a} : Set V) at hv
              simpa only [Set.mem_singleton_iff] using hv
            exact (hvNotA hva).elim
          · apply hQ.2.2.2 (u : V) huQ (v : V)
            · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvC⟩
            · exact huv
        exact ih hvQ
  have hwQ : w ∈ Q := walk_stays_in_Q p (by simpa [zz] using hzQ)
  exact (Finset.mem_sdiff.mp (hQ.2.1 hwQ)).2 hwC

end
end Erdos767
