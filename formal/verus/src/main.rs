// T9 PILOT: one property, verified with Verus on a COPY of the dag.rs logic.
//
// Property (unbounded): for ANY bundle length and ANY depth limit, if the
// delegation walk of authgate-kernel/src/tcb/dag.rs::validate_chain returns Ok,
// then there is a path leaf -> ... -> root through the bundle (each step a
// parent_hash link) such that every node on it has rights that are a superset
// of the leaf's rights; in particular leaf.rights ⊆ root.rights. No rights are
// ever escalated along the chain.
//
// Mirror of formal/kani/prop_chain.rs::proof_attenuation_two_node, but for
// chains of arbitrary length (loop invariant, no unrolling).
//
// Trusted modelling assumptions (NOT verified here):
//  A1. Signature and SHA-256 issuer-identity checks of dag.rs are (epoch + resource ARE modelled)
//      omitted. They only add early `Err` returns, so the model accepts a
//      superset of what dag.rs accepts; a property of the model's Ok implies
//      the property for dag.rs's Ok.
//  A2. proof_hash / parent_hash are modelled as u64 (dag.rs: 32-byte arrays);
//      equality semantics are the same.
//  A3. The loop is a hand-copied transcription of dag.rs; nothing mechanically
//      ties it to the Rust source (correspondence is by review).
//  A4. `max_depth` is a parameter (dag.rs: MAX_CHAIN_DEPTH = 16); the proof holds for all values.
use vstd::prelude::*;

verus! {

pub struct Node {
    pub hash: u64,
    /// None = IssuerRef::Root, Some(h) = IssuerRef::Delegated { parent_hash: h }
    pub parent: Option<u64>,
    pub rights: u64,
    /// dag.rs: ProofNode.epoch, checked on every hop (AT-3.1)
    pub epoch: u64,
    /// dag.rs: ProofNode.resource_hash (32 bytes there, u64 here; equality only)
    pub resource: u64,
}

/// a ⊆ b  <=>  (a & !b) == 0   (the exact test used in dag.rs line 100)
pub open spec fn subset(a: u64, b: u64) -> bool {
    a & !b == 0
}

proof fn subset_trans(a: u64, b: u64, c: u64)
    requires subset(a, b), subset(b, c),
    ensures subset(a, c),
{
    assert(a & !b == 0 && b & !c == 0 ==> a & !c == 0) by (bit_vector);
}

proof fn subset_refl(a: u64)
    ensures subset(a, a),
{
    assert(a & !a == 0) by (bit_vector);
}

/// `path` is a genuine delegation path in `bundle` ending at a root node.
pub open spec fn valid_path(bundle: Seq<Node>, leaf: int, path: Seq<int>) -> bool {
    &&& path.len() >= 1
    &&& path[0] == leaf
    &&& forall|k: int| 0 <= k < path.len() ==> 0 <= #[trigger] path[k] < bundle.len()
    &&& forall|k: int| 0 <= k < path.len() - 1 ==>
            bundle[#[trigger] path[k]].parent == Some(bundle[path[k + 1]].hash)
    &&& bundle[path[path.len() - 1]].parent.is_none()
    // attenuation at every step
    &&& forall|k: int| 0 <= k < path.len() - 1 ==>
            subset(bundle[#[trigger] path[k]].rights, bundle[path[k + 1]].rights)
}

/// Exec: first node whose hash matches (dag.rs: `all_proofs.iter().find(..)`).
fn find(bundle: &Vec<Node>, h: u64) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < bundle.len() && bundle[i as int].hash == h,
            None => true,
        },
{
    let mut i = 0usize;
    while i < bundle.len()
        invariant i <= bundle.len(),
        decreases bundle.len() - i,
    {
        if bundle[i].hash == h {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Copy of the dag.rs walk loop (rights/attenuation + parent lookup + depth limit only).
pub fn walk(bundle: &Vec<Node>, leaf: usize, max_depth: usize, min_epoch: u64) -> (r: Result<u64, ()>)
    requires leaf < bundle.len(), max_depth < 0xffff_ffffusize,
    ensures
        match r {
            Ok(root_rights) => exists|path: Seq<int>|
                valid_path(bundle@, leaf as int, path)
                && bundle@[path[path.len() - 1]].rights == root_rights
                // unbounded conclusion: leaf rights ⊆ rights of EVERY node on the path
                && (forall|k: int| 0 <= k < path.len() ==>
                        subset(bundle@[leaf as int].rights, #[trigger] bundle@[path[k]].rights))
                && subset(bundle@[leaf as int].rights, root_rights)
                // every node on the path (including the root) has epoch >= min_epoch
                && (forall|k: int| 0 <= k < path.len() ==> #[trigger] bundle@[path[k]].epoch >= min_epoch)
                // resource propagation: every node on the path is for the leaf's resource
                && (forall|k: int| 0 <= k < path.len() ==> #[trigger] bundle@[path[k]].resource == bundle@[leaf as int].resource),
            Err(_) => true,
        },
{
    let leaf_rights = bundle[leaf].rights;
    let mut cur = leaf;
    let mut depth = 0usize;
    let ghost mut path: Seq<int> = seq![leaf as int];
    proof { subset_refl(leaf_rights); }

    loop
        invariant
            cur < bundle.len(),
            path.len() >= 1,
            path[0] == leaf as int,
            path[path.len() - 1] == cur as int,
            forall|k: int| 0 <= k < path.len() ==> 0 <= #[trigger] path[k] < bundle.len(),
            forall|k: int| 0 <= k < path.len() - 1 ==>
                bundle@[#[trigger] path[k]].parent == Some(bundle@[path[k + 1]].hash),
            forall|k: int| 0 <= k < path.len() - 1 ==>
                subset(bundle@[#[trigger] path[k]].rights, bundle@[path[k + 1]].rights),
            forall|k: int| 0 <= k < path.len() ==>
                subset(leaf_rights, #[trigger] bundle@[path[k]].rights),
            leaf_rights == bundle@[leaf as int].rights,
            forall|k: int| 0 <= k < path.len() - 1 ==> #[trigger] bundle@[path[k]].epoch >= min_epoch,
            forall|k: int| 0 <= k < path.len() ==> #[trigger] bundle@[path[k]].resource == bundle@[leaf as int].resource,
            depth <= max_depth + 1,
            max_depth < 0xffff_ffffusize,
        decreases max_depth + 1 - depth,
    {
        if depth > max_depth {
            return Err(());
        }
        depth += 1;

        // dag.rs: `if current.epoch < min_epoch { return Err(..) }` on every hop
        if bundle[cur].epoch < min_epoch {
            return Err(());
        }

        match bundle[cur].parent {
            None => {
                // IssuerRef::Root
                proof {
                    assert(valid_path(bundle@, leaf as int, path));
                    assert(subset(leaf_rights, bundle@[cur as int].rights));
                }
                return Ok(bundle[cur].rights);
            }
            Some(ph) => {
                let p = match find(bundle, ph) {
                    Some(i) => i,
                    None => { return Err(()); }
                };
                // Resource propagation: dag.rs line 82
                if bundle[cur].resource != bundle[p].resource {
                    return Err(());
                }
                // Attenuation: dag.rs line 100
                if (bundle[cur].rights & !bundle[p].rights) != 0 {
                    return Err(());
                }
                proof {
                    let old = path;
                    subset_trans(leaf_rights, bundle@[cur as int].rights, bundle@[p as int].rights);
                    path = old.push(p as int);
                    assert(path.len() == old.len() + 1);
                    assert forall|k: int| 0 <= k < path.len() implies
                        #[trigger] bundle@[path[k]].resource == bundle@[leaf as int].resource by {
                        if k < old.len() { assert(path[k] == old[k]); }
                    }
                    assert forall|k: int| 0 <= k < path.len() implies
                        subset(leaf_rights, #[trigger] bundle@[path[k]].rights) by {
                        if k < old.len() { assert(path[k] == old[k]); }
                    }
                    assert forall|k: int| 0 <= k < path.len() - 1 implies
                        bundle@[#[trigger] path[k]].parent == Some(bundle@[path[k + 1]].hash) by {
                        if k < old.len() - 1 { assert(path[k] == old[k]); assert(path[k+1] == old[k+1]); }
                        else { assert(path[k] == old[old.len() - 1]); }
                    }
                    assert forall|k: int| 0 <= k < path.len() - 1 implies
                        subset(bundle@[#[trigger] path[k]].rights, bundle@[path[k + 1]].rights) by {
                        if k < old.len() - 1 { assert(path[k] == old[k]); assert(path[k+1] == old[k+1]); }
                        else { assert(path[k] == old[old.len() - 1]); }
                    }
                }
                cur = p;
            }
        }
    }
}

fn main() {}

} // verus!
