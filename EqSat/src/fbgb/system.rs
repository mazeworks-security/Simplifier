use crate::{bool_poly::BoolPoly, transforms::fast_anf_transform};

#[inline(never)]
pub fn get_truth_table_system<const N: usize>(truth_table: BoolPoly<N>) -> Vec<BoolPoly<N>>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let num_equations = truth_table.popcount();
    let mut system = Vec::with_capacity(num_equations as usize);
    for i in 0..BoolPoly::<N>::BIT_SIZE {
        if !truth_table.has_bit(i) {
            continue;
        }

        let mut dnf_row = BoolPoly::<N>::new();
        dnf_row.set_bit(i, true);

        let anf_row = fast_anf_transform(&dnf_row);
        system.push(anf_row);
    }
    system
}
