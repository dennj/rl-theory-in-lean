import Mathlib.MeasureTheory.MeasurableSpace.Constructions

lemma Measurable.of_uncurry
  {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {f : α → β → γ} (h : Measurable (Function.uncurry f))
  : Measurable f := by
    apply measurable_pi_iff.mpr
    intro a
    apply Measurable.of_uncurry_right h
