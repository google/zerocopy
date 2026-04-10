/// ```lean, hermes, spec
/// ensures: ret.val = 0
/// proof:
///   unfold get_size_of_empty_tuple at h_returns
///   simp_all
///   subst ret
///   rfl
/// proof (h_progress):
///   unfold get_size_of_empty_tuple
///   simp_all
/// ```
pub fn get_size_of_empty_tuple() -> usize {
    core::mem::size_of::<()>()
}

/// ```lean, hermes, spec
/// ensures: ret.val = 1
/// proof:
///   unfold get_align_of_empty_tuple at h_returns
///   simp_all
///   subst ret
///   rfl
/// proof (h_progress):
///   unfold get_align_of_empty_tuple
///   simp_all
/// ```
pub fn get_align_of_empty_tuple() -> usize {
    core::mem::align_of::<()>()
}

/// ```hermes
/// requires: ∃ (_sz : Hermes.core.marker.Sized T) (tl : Hermes.HasStaticLayout T), True
/// ensures: match core.mem.size_of T with
///   | Result.ok size => ret.val = size.val
///   | _ => False
/// proof:
///   rcases h_anon with ⟨_sz, tl, _⟩
///   have h_wp : Aeneas.Std.WP.spec (silly_size_of _val) (fun r => r.val = (Hermes.HasStaticLayout.layout T).size.val) := by
///     unfold silly_size_of
///     have h_align_pos : 0 < (Hermes.HasStaticLayout.layout T).align.val.val := (Hermes.HasStaticLayout.layout T).align.isValid.left
///     have h_align_nz : (Hermes.HasStaticLayout.layout T).align.val.val ≠ 0 := by omega
///     simp_all
///     step
///     step
///     · rw [i_post]
///       simp
///     · rw [i_post] at r_post
///       simp at r_post
///       exact r_post
///   have ⟨y, hy1, hy2⟩ := Aeneas.Std.WP.spec_imp_exists h_wp
///   simp_all
/// proof (h_progress):
///   rcases h_req with ⟨_, ⟨_sz, tl, _⟩⟩
///   have h_wp : Aeneas.Std.WP.spec (silly_size_of _val) (fun _ => True) := by
///     unfold silly_size_of
///     have h_align_pos : 0 < (Hermes.HasStaticLayout.layout T).align.val.val := (Hermes.HasStaticLayout.layout T).align.isValid.left
///     have h_align_nz : (Hermes.HasStaticLayout.layout T).align.val.val ≠ 0 := by omega
///     simp_all
///     step
///     step
///     · rw [i_post]
///       simp
///   have ⟨y, hy1, _⟩ := Aeneas.Std.WP.spec_imp_exists h_wp
///   exact ⟨y, hy1⟩
/// ```
pub unsafe fn silly_size_of<T>(_val: *const T) -> usize {
    let size = core::mem::size_of::<T>();
    let align = core::mem::align_of::<T>();
    (size / align) * align
}

fn main() {}
