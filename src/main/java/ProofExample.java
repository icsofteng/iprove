import com.microsoft.z3.*;
import com.sun.org.apache.xpath.internal.operations.Bool;

import java.util.HashMap;

public class ProofExample {

    public static void main(String[] args) {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("proof", "true");
//        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        ProofExample example = new ProofExample();
        example.proveExample(ctx);
        example.proveExample2(ctx);
        example.proveExample3(ctx);
        example.proveExample4(ctx);
        example.proveExample5(ctx);


        String name = "Toma";

    }

    public void proveExample(Context ctx) {
//
        BoolExpr p = ctx.mkBoolConst("p");
        BoolExpr q = ctx.mkBoolConst("q");
        BoolExpr pImpliesQ = ctx.mkImplies(p, q);
        prove(ctx, q, false, p, pImpliesQ);

    }
    public void proveExample2(Context ctx) {
        BoolExpr p = ctx.mkBoolConst("p");
        BoolExpr q = ctx.mkBoolConst("q");
        prove(ctx, ctx.mkAnd(p, q), false, p, q);
    }

    public void proveExample3(Context ctx) {
        BoolExpr p = ctx.mkBoolConst("p");
        BoolExpr q = ctx.mkBoolConst("q");
        BoolExpr r = ctx.mkBoolConst("r");
        prove(ctx, ctx.mkImplies(p, r), false, ctx.mkImplies(p, q), ctx.mkImplies(q, r));
    }

    public void proveExample4(Context ctx) {
        BoolExpr p = ctx.mkBoolConst("p");
        BoolExpr q = ctx.mkBoolConst("q");
        BoolExpr r = ctx.mkBoolConst("r");
        BoolExpr s = ctx.mkBoolConst("s");

        BoolExpr pIq = ctx.mkImplies(p, q);
        BoolExpr npIr = ctx.mkImplies(ctx.mkNot(p), r);
        BoolExpr qIs = ctx.mkImplies(q, s);
        BoolExpr rIs = ctx.mkImplies(r, s);

        prove(ctx, s, false, pIq, npIr, qIs, rIs);
    }

    public void proveExample5(Context ctx) {
        BoolExpr p = ctx.mkBoolConst("p");
        BoolExpr c = ctx.mkBoolConst("c");
        BoolExpr n = ctx.mkBoolConst("n");
        BoolExpr t = ctx.mkBoolConst("t");
        BoolExpr h = ctx.mkBoolConst("h");
        BoolExpr s = ctx.mkBoolConst("s");

        BoolExpr cAnIt = ctx.mkImplies(ctx.mkAnd(c,n),t);
        BoolExpr hANs = ctx.mkAnd(h, ctx.mkNot(s));
        BoolExpr hANsVcIp = ctx.mkImplies(ctx.mkAnd(h, ctx.mkNot(ctx.mkOr(s, c))), p);

        BoolExpr nANtIp = ctx.mkImplies(ctx.mkAnd(n, ctx.mkNot(t)),p);

        prove(ctx, nANtIp, false, cAnIt, hANs, hANsVcIp);

    }

    public void prove(Context ctx, BoolExpr target, boolean useMBQI, BoolExpr... assumptions) {
        System.out.println("Proving: " + target);
        Solver s = ctx.mkSolver();
        Params p = ctx.mkParams();
        p.add("mbqi", useMBQI);
        s.setParameters(p);
        for (BoolExpr a : assumptions)
            s.add(a);
        Status q = s.check(ctx.mkNot(target));
        System.out.println("Assumptions:");
        for (BoolExpr assertion : s.getAssertions()) {
            System.out.println(assertion);
        }
        switch (q)
        {
            case UNKNOWN:
                System.out.println("Unknown because: " + s.getReasonUnknown());
                break;
            case SATISFIABLE:
                System.out.println("NOT OK, " + target + " not a valid (always true) expression");
                break;
            case UNSATISFIABLE:
                System.out.println("OK, proof: " + s.getProof());
                break;
        }
    }
}
