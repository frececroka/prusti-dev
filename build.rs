extern crate jni_gen;
extern crate env_logger;
extern crate error_chain;

use std::fs;
use std::env;
use jni_gen::*;
use error_chain::ChainedError;

fn main() {
    env_logger::init().expect("failed to initialize env_logger");
    let generated_dir = format!("{}/gen", env::var("CARGO_MANIFEST_DIR").unwrap());
    let asm_jar = env::var("ASM_JAR").unwrap();

    let mut viper_jars: Vec<String> = fs::read_dir("/usr/lib/viper/")
        .unwrap()
        .map(|x| x.unwrap().path().to_str().unwrap().to_owned())
        .collect();

    WrapperGenerator::new()
        .use_jar(&asm_jar)
        .use_jars(&mut viper_jars)
        .wrap_all(&vec![
            // Java
            "java.lang.Object",
            "java.lang.System",
            "java.io.PrintStream",
            "java.math.BigInteger",
            "java.nio.file.Paths",
            // Scala
            "scala.Some",
            "scala.None$",
            "scala.Predef",
            "scala.math.BigInt",
            "scala.collection.mutable.ArraySeq",
            "scala.collection.mutable.ListBuffer",
            "scala.collection.immutable.HashMap",
            // Viper
            "viper.silicon.Silicon",
            "viper.silver.ast.Add",
            "viper.silver.ast.AddOp$",
            "viper.silver.ast.And",
            "viper.silver.ast.AndOp$",
            "viper.silver.ast.AnySetContains",
            "viper.silver.ast.AnySetUnion",
            "viper.silver.ast.Assert",
            "viper.silver.ast.Bool$",
            "viper.silver.ast.CondExp",
            "viper.silver.ast.CurrentPerm",
            "viper.silver.ast.Div",
            "viper.silver.ast.DivOp$",
            "viper.silver.ast.Domain",
            "viper.silver.ast.DomainAxiom",
            "viper.silver.ast.DomainFunc",
            "viper.silver.ast.DomainFuncApp",
            "viper.silver.ast.DomainType",
            "viper.silver.ast.EmptySeq",
            "viper.silver.ast.EmptySet",
            "viper.silver.ast.EqCmp",
            "viper.silver.ast.Exhale",
            "viper.silver.ast.Exists",
            "viper.silver.ast.ExplicitSeq",
            "viper.silver.ast.ExplicitSet",
            "viper.silver.ast.FalseLit",
            "viper.silver.ast.Field",
            "viper.silver.ast.FieldAccess",
            "viper.silver.ast.FieldAccessPredicate",
            "viper.silver.ast.FieldAssign",
            "viper.silver.ast.Fold",
            "viper.silver.ast.Forall",
            "viper.silver.ast.ForPerm",
            "viper.silver.ast.FracOp$",
            "viper.silver.ast.FractionalPerm",
            "viper.silver.ast.FullPerm",
            "viper.silver.ast.FuncApp",
            "viper.silver.ast.Function",
            "viper.silver.ast.GeCmp",
            "viper.silver.ast.GeOp$",
            "viper.silver.ast.Goto",
            "viper.silver.ast.GtCmp",
            "viper.silver.ast.GtOp$",
            "viper.silver.ast.IdentifierPosition",
            "viper.silver.ast.If",
            "viper.silver.ast.Implies",
            "viper.silver.ast.ImpliesOp$",
            "viper.silver.ast.Inhale",
            "viper.silver.ast.InhaleExhaleExp",
            "viper.silver.ast.Int$",
            "viper.silver.ast.IntLit",
            "viper.silver.ast.IntPermMul",
            "viper.silver.ast.IntPermMulOp$",
            "viper.silver.ast.Label",
            "viper.silver.ast.LeCmp",
            "viper.silver.ast.LeOp$",
            "viper.silver.ast.Let",
            "viper.silver.ast.LineColumnPosition",
            "viper.silver.ast.LocalVar",
            "viper.silver.ast.LocalVarAssign",
            "viper.silver.ast.LocalVarDecl",
            "viper.silver.ast.LtCmp",
            "viper.silver.ast.LtOp$",
            "viper.silver.ast.Method",
            "viper.silver.ast.MethodCall",
            "viper.silver.ast.Minus",
            "viper.silver.ast.Mod",
            "viper.silver.ast.ModOp$",
            "viper.silver.ast.Mul",
            "viper.silver.ast.MulOp$",
            "viper.silver.ast.NeCmp",
            "viper.silver.ast.NegOp$",
            "viper.silver.ast.NewStmt",
            "viper.silver.ast.NoInfo$",
            "viper.silver.ast.NoPerm",
            "viper.silver.ast.NoPosition$",
            "viper.silver.ast.Not",
            "viper.silver.ast.NotOp$",
            "viper.silver.ast.NoTrafos$",
            "viper.silver.ast.NullLit",
            "viper.silver.ast.Old",
            "viper.silver.ast.Or",
            "viper.silver.ast.OrOp$",
            "viper.silver.ast.Perm$",
            "viper.silver.ast.PermAdd",
            "viper.silver.ast.PermAddOp$",
            "viper.silver.ast.PermDivOp$",
            "viper.silver.ast.PermGeCmp",
            "viper.silver.ast.PermGtCmp",
            "viper.silver.ast.PermLeCmp",
            "viper.silver.ast.PermLtCmp",
            "viper.silver.ast.PermMinus",
            "viper.silver.ast.PermMul",
            "viper.silver.ast.PermSub",
            "viper.silver.ast.Predicate",
            "viper.silver.ast.PredicateAccess",
            "viper.silver.ast.PredicateAccessPredicate",
            "viper.silver.ast.Program",
            "viper.silver.ast.Ref$",
            "viper.silver.ast.Result",
            "viper.silver.ast.SeqAppend",
            "viper.silver.ast.SeqContains",
            "viper.silver.ast.SeqDrop",
            "viper.silver.ast.SeqIndex",
            "viper.silver.ast.SeqLength",
            "viper.silver.ast.Seqn",
            "viper.silver.ast.SeqTake",
            "viper.silver.ast.SeqType",
            "viper.silver.ast.SetType",
            "viper.silver.ast.SimpleInfo",
            "viper.silver.ast.Sub",
            "viper.silver.ast.SubOp$",
            "viper.silver.ast.Trigger",
            "viper.silver.ast.TrueLit",
            "viper.silver.ast.TypeVar",
            "viper.silver.ast.Unfold",
            "viper.silver.ast.Unfolding",
            "viper.silver.ast.utility.QuantifiedPermissions$",
            "viper.silver.ast.While",
            "viper.silver.ast.WildcardPerm",
        ])
        .generate(&generated_dir)
        .unwrap_or_else(|e| {
            panic!(format!("{}", e.display_chain().to_string()));
        });
}
