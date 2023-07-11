use egg::*;

// TODO:
// * Async?
//
// * MetaStructure
//   - Each bit of a structure and it's substructures
//     gets expanded into a flat array of MetaBit:s.
//
// * MetaSkeleton
//     - Represents the packet structure as an
//       unsafe tree of values. (Each value may be garbage, represented with MaybeUninit)
//
//     - Has a MetaSkeletonState that stores the state of each Metabyte object,
//       e.g. SkeletonNodeState::Finalized, SkeletonNodeState::Waiting(EarlyAccessWaitGroup)
//
// * EarlyAccessWaitGroup
//     - Represents a list bits for which a Metabyte objects needs to be finalized.
//
//     - Used for determining when to attempt parsing of an object again by
//       finding the MetaBit with the highest EarlyAccessIndex in the list
//       of MetaBit's this wait group is waiting for. 
//
// * OwningByte
//     - TODO: Doc
//
// * MetaBit
//     - OwningByte; The byte that this bit originally came from.
//
//     - EarlyAccessIndex; The MetaBit's index in the flat MetaBit array.
//
// * The MetaOpt/E-Graph will optimize according to different weights and parameters.
//     - Optimize blob size based on SIZE_WEIGHT. This optimization may reorder
//       the MetaBit:s so that bytes with limited ranges will all fit in the same byte.
//
//     - Optimize early access, introducing EARLY_ACCESS_WEIGHT.
//       The early access property describes how early an object may be finalized. If the
//       EARLY_ACCESS_WEIGHT for a particular object is very high, all it's MetaBit:s
//       will stay relatively close to eachother, and will come early in the stream.
//       This may be useful if you desire to access only a particular set of fields
//       on the packet, or an array length. Array length fields or other types of fields
//       that represent some variable length, will benefit from a high EARLY_ACCESS_WEIGHT
//       because the EarlyAccessWaitGroup can more accurately tell how many bytes it will need
//       before continuing parsing (minimum).
//
//     - Optimize MetaBit:s will end up in the same byte it originated from. This means
//       better performance for reading bytes because no bitshifting and stuff has to be done to
//       actually read a single byte into an object, and less complex EarlyAccessWaitGroup:s.
//       Say, for example, that we need to read a u128
//       from the stream. This will result in very poor performance if we have to locate each bit
//       of the u128 structure (8*128=1024 bits!!). Therefore it would be good if a
//       BYTE_LOCALITY_WEIGHT is introduced that will keep the bits in a reasonable place for
//       larger objects.

define_language! {
    enum SimpleLanguage {
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Symbol(Symbol),
    }
}

define_language! {
    enum Metabyte {
        "struct" =  Struct([Id; 2]),

        "m1" = Meta1(Id),
        "m2" = Meta2([Id; 2]),
        "m3" = Meta3([Id; 2]),
        "m4" = Meta4([Id; 2]),
        "m5" = Meta5([Id; 2]),
        "m6" = Meta6([Id; 2]),
        "m7" = Meta7([Id; 2]),
        "m8" = Meta8([Id; 2]),

        "unit" = MetaUnit,
        Byte(Symbol),
        // Const(u8),
    }
}

fn metabyte_rules() -> Vec<Rewrite<Metabyte, ()>> {
    vec![
        rewrite!("commute-m2"; "(m2 ?x ?y)" => "(m2 ?y ?x)"),
        rewrite!("commute-m3"; "(m3 ?x ?y)" => "(m3 ?y ?x)"),
        rewrite!("promote-m1-m2"; "(struct (m1 ?merge) (struct (m1 ?y) ?rest))" => "(struct (m2 ?merge ?y) ?rest)"),
        rewrite!("promote-m2-m3"; "(struct (m1 ?merge) (struct (m2 ?y ?z) ?rest))" => "(struct (m3 ?merge (m2 ?y ?z)) ?rest)"),
        rewrite!("promote-m3-m4"; "(struct (m1 ?merge) (struct (m3 ?m3_x (m2 ?m2_x ?m2_y)) ?rest))" => "(struct (m4 ?merge (m3 ?m3_x (m2 ?m2_x ?m2_y))) ?rest)"),
        rewrite!("promote-m4-m5"; "(struct (m1 ?merge) (struct (m4 ?m4_x (m3 ?m3_x (m2 ?m2_x ?m2_y))) ?rest))" => "(struct (m5 ?merge (m4 ?m4_x (m3 ?m3_x (m2 ?m2_x ?m2_y)))) ?rest)"),
        rewrite!("promote-m5-m6"; "(struct (m1 ?merge) (struct (m5 ?m5_x (m4 ?m4_x (m3 ?m3_x (m2 ?m2_x ?m2_y)))) ?rest))" => "(struct (m6 ?merge (m5 ?m5_x (m4 ?m4_x (m3 ?m3_x (m2 ?m2_x ?m2_y))))) ?rest)"),
        rewrite!("promote-m6-m7"; "(struct (m1 ?merge) (struct (m6 ?m6_x (m5 ?m5_x (m4 ?m4_x (m3 ?m3_x (m2 ?m2_x ?m2_y))))) ?rest))" => "(struct (m7 ?merge (m6 ?m6_x (m5 ?m5_x (m4 ?m4_x (m3 ?m3_x (m2 ?m2_x ?m2_y)))))) ?rest)"),
        rewrite!("promote-m7-m8"; "(struct (m1 ?merge) (struct (m7 ?m7_x (m6 ?m6_x (m5 ?m5_x (m4 ?m4_x (m3 ?m3_x (m2 ?m2_x ?m2_y)))))) ?rest))" => "(struct (m8 ?merge (m7 ?m7_x (m6 ?m6_x (m5 ?m5_x (m4 ?m4_x (m3 ?m3_x (m2 ?m2_x ?m2_y))))))) ?rest)"),
    ]
}

struct MetabyteCostFunction;
impl CostFunction<Metabyte> for MetabyteCostFunction {
    type Cost = usize;

    fn cost<C>(&mut self, enode: &Metabyte, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let cost = match enode {
            Metabyte::Byte(_) => 1,
            Metabyte::Meta1(_) => 1,
            Metabyte::Meta2(_) => 1,
            Metabyte::Meta3(_) => 1,
            Metabyte::Meta4(_) => 1,
            Metabyte::Meta5(_) => 1,
            Metabyte::Meta6(_) => 1,
            Metabyte::Meta7(_) => 1,
            Metabyte::Meta8(_) => 1,
            Metabyte::MetaUnit => 0,
            Metabyte::Struct(_) => enode.fold(0, |sum, id| sum + costs(id)),
        };
        log::info!("Cost function called for {enode:?}, cost {cost}");
        cost
    }
}

/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(s: &str) -> (usize, String) {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<Metabyte> = s.parse().unwrap();
    log::warn!("cost of {expr:?}: {}", MetabyteCostFunction.cost_rec(&expr));

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let runner = Runner::default().with_expr(&expr).run(&metabyte_rules());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, MetabyteCostFunction);
    let (best_cost, best) = extractor.find_best(root);
    log::warn!("Simplified {} to {} with cost {}", expr, best, best_cost);
    (best_cost, best.to_string())
}

fn test_merge(amount: u8) {
    let mut buf = String::new();
    if amount == 0 {
        buf.push_str("(struct unit unit)");
    } else {
        for _ in 0..amount {
            buf.push_str("(struct (m1 1) ");
        }
        buf.push_str("unit");
        for _ in 0..amount {
            buf.push(')');
        }
    }
    log::info!("Testing merge {buf}");
    let (cost, out) = simplify(&buf);

    assert_eq!(cost, if amount == 0 { 0 } else { 1 });
    // TODO: Generate for output
    assert!(!out.is_empty());
}

#[test]
fn simple_tests() {
    env_logger::init();
    for n in 0..=8 {
        test_merge(n);
    }
    //assert_eq!(simplify("(* 0 42)"), "0");
    //assert_eq!(simplify("(+ 0 (* 1 foo))"), "foo");
}

fn main() {
    env_logger::init();
    eprintln!("{:?}", std::hint::black_box(test_merge(8)));
}
