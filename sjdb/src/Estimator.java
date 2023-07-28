//package sjdb;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

/**
 * Implement PlanVisitor
 * Calculate the cost of each operator and get the final cost by sum them
 * create a relation for each operator as output
 */
public class Estimator implements PlanVisitor {
    //Overall cost of the plan
    public int cost = 0;


    public Estimator() {
        // empty constructor
    }

    /*
     * Create output relation on Scan operator
     *
     * Example implementation of visit method for Scan operators.
     */
    public void visit(Scan op) {
        Relation input = op.getRelation();
        Relation output = new Relation(input.getTupleCount());
        Iterator<Attribute> iter = input.getAttributes().iterator();
        while (iter.hasNext()) {
            output.addAttribute(new Attribute(iter.next()));
        }
        op.setOutput(output);
        cost += input.getTupleCount();
    }

    public void visit(Project op) {
        //PROJECT [attr-list] (input)

        //Get info of input-relation
        Relation input = op.getInput().getOutput();

        //Set output-relation
        // 1. output-size = T(PROJECT [attr-list] (input)) = T(input)
        Relation output = new Relation(input.getTupleCount());
        // 2. output-attr = attr-list
        Iterator<Attribute> iter = op.getAttributes().iterator();
        while (iter.hasNext()) {
            // loop attr in attr-list (attr that need to be kept)
            Attribute attrKept = new Attribute(iter.next());
            // find attrKept in input, add it to output
            try {
                // if find successful
                output.addAttribute(input.getAttribute(attrKept));
            } catch (Exception e) {
                // if cant find attrKept in input
                // do nothing
            }
        }
        // 3. set output
        op.setOutput(output);

        //Add to cost
        // cost += output-size
        cost += output.getTupleCount();

    }

    public void visit(Select op) {
        //SELECT [predicate] (input)
        // !!! attr.values CHANGE !!!

        // !!! TWO SPECIAL CASE !!!
        // Case1: Division by zero (output empty R with empty attr),
        // Case2: Can't find attr (output empty R with no attr)

        //Get info of input-relation
        Relation input = op.getInput().getOutput();

        //Set output-relation
        Relation output;

        //Get info of predicate: attrLeft, attrRight
        //Calculate V(input, attrLeft) and V(input, attrRight) for future devision
        Attribute attrLeft = null;
        Attribute attrRight = null;
        int vLeft = 0;//V(input, attrLeft)
        int vRight = 0;//V(input, attrRight)

        boolean isEqualValue = op.getPredicate().equalsValue();
        if (isEqualValue) {
            // predicate: attr=value
            attrLeft = op.getPredicate().getLeftAttribute();
            try {
                vLeft = input.getAttribute(attrLeft).getValueCount();
            } catch (Exception e) {
                // case2, can't find attr
                output = new Relation(0);
                // no attr
                // cost += 0;
                return;
            }
        } else {
            //predicate: attr=attr
            attrLeft = op.getPredicate().getLeftAttribute();
            attrRight = op.getPredicate().getRightAttribute();
            try {
                vLeft = input.getAttribute(attrLeft).getValueCount();
                vRight = input.getAttribute(attrRight).getValueCount();
            } catch (Exception e) {
                // case2, can't find attr
                output = new Relation(0);
                // no attr
                // cost += 0;
                return;
            }
        }


        //Set output relation
        int values = 0;// V(output, attr)
        if (isEqualValue) {
            //IF attr = value
            // 1. output-size = T(SELECT [attrLeft=value] (input)) = T(input) / V(input, attrLeft)
            // output-size = T(input)/vLeft
            if (vLeft == 0) {
                // case1: devision by zero
                output = new Relation(0);
            } else {
                output = new Relation(input.getTupleCount() / vLeft);
            }

            // 2.(calculate) output-attr = predicate-attr && V(output, attrLeft) = 1
            values = 1;

        } else {
            //IF attr = attr
            // 1. output-size = T(SELECT [attrLeft=attrRight] (input))
            // = T(input) / max(V(input, attrLeft), V(input, attrRight))
            // output-size = T(input) / max(vLeft, vRight)
            int vMax = Math.max(vLeft, vRight);
            if (vMax == 0) {
                // case1, devision by zero
                output = new Relation(0);
            } else {
                output = new Relation(input.getTupleCount() / vMax);
            }

            // 2.(calculate) output-attr = predicate-attr &&
            // V(out, attr) = min(V(input, attrLeft), V(input, attrRight))
            values = Math.min(vLeft, vRight);
        }

        // V(R, attr) <= T(R)
        int maxT = output.getTupleCount();
        values = Math.min(maxT, values);

        // 2.(implement) output-attr = input-attr && V CHANGE
        Iterator<Attribute> iter = input.getAttributes().iterator();
        while (iter.hasNext()) {
            Attribute attr = new Attribute(iter.next());
            if (attr.equals(attrLeft)) {
                output.addAttribute(new Attribute(attr.getName(), values));
            } else if (attr.equals(attrRight)) {
                output.addAttribute(new Attribute(attr.getName(), values));
            } else {
                output.addAttribute(new Attribute(attr.getName(), Math.min(maxT, attr.getValueCount())));
            }
        }

        // 3. set out put
        op.setOutput(output);

        //Add to cost
        //cost += output-size
        cost += output.getTupleCount();
    }

    public void visit(Product op) {
        // left-op PRODUCT right-op

        //Get info of input-relation: left, right
        Relation inputLeft = op.getLeft().getOutput();
        Relation inputRight = op.getRight().getOutput();

        //Set output-relation
        // 1. output-size = T(left X right) = T(left)*T(right)
        Relation output = new Relation(inputLeft.getTupleCount() * inputRight.getTupleCount());

        // 2. output-attr = left-attr + right-attr
        Iterator<Attribute> iterLeft = inputLeft.getAttributes().iterator();
        while (iterLeft.hasNext()) {
            output.addAttribute(new Attribute(iterLeft.next()));
        }
        Iterator<Attribute> iterRight = inputRight.getAttributes().iterator();
        while (iterRight.hasNext()) {
            output.addAttribute(new Attribute(iterRight.next()));
        }

        // 3. set output
        op.setOutput(output);

        //Add to cost
        //cost += output-size
        cost += output.getTupleCount();
    }

    public void visit(Join op) {
        // left-op JOIN right-op
        // !!! attr.values CHANGE !!!

        // !!! TWO SPECIAL CASE !!!
        // Case1: Division by zero (output empty R with empty attr),
        // Case2: Can't find attr (output empty R with no attr)

        //Get info of input-relation: inputLeft, inputRight
        Relation inputLeft = op.getLeft().getOutput();
        Relation inputRight = op.getRight().getOutput();

        //Set output-relation
        Relation output;

        //Get info of predicate: attrLeft, attrRight
        Attribute attrLeft = op.getPredicate().getLeftAttribute();
        Attribute attrRight = op.getPredicate().getRightAttribute();

        //Calculate vLeft, vRight for future devision
        int vLeft = 0;
        int vRight = 0;
        try {
            vLeft = inputLeft.getAttribute(attrLeft).getValueCount();
            vRight = inputRight.getAttribute(attrRight).getValueCount();
        } catch (Exception e) {
            // case2: can't find attr
            output = new Relation(0);
            //no attr
            op.setOutput(output);
            //cost += 0
            return;
        }


        //Set output-relation
        // 1. T(output)
        // = (T(inputLeft)*T(inputRight)) / max(V(inputLeft, attrLeft), V(inputRight, attrRight))
        int vMax = Math.max(vLeft, vRight);
        if (vMax == 0) {
            //case1: devision by zero
            output = new Relation(0);
        } else {
            output = new Relation(inputLeft.getTupleCount() * inputRight.getTupleCount() / vMax);
        }

        // 2. output-attr = inputLeft-attr + inputRight-attr
        // && V(output, L or R attr) = min(V(inputLeft, attrLeft), V(inputRight, attrRight))
        // && V(output, other attr) = V(input, other attr)
        //V() <= T(R)
        int maxT = output.getTupleCount();
        int values = Math.min(Math.min(vLeft, vRight), maxT);//V(R, L or R attr)
        // Left Relation
        Iterator<Attribute> iterLeft = inputLeft.getAttributes().iterator();
        while (iterLeft.hasNext()) {
            Attribute attr = new Attribute(iterLeft.next());
            if (attr.equals(attrLeft)) {
                // left attr
                output.addAttribute(new Attribute(attr.getName(), values));
            } else {
                //other attr V() <= T(R)
                output.addAttribute(new Attribute(attr.getName(), Math.min(maxT, attr.getValueCount())));
            }
        }
        // Right Relation
        Iterator<Attribute> iterRight = inputRight.getAttributes().iterator();
        while (iterRight.hasNext()) {
            Attribute attr = new Attribute(iterRight.next());
            if (attr.equals(attrRight)) {
                // right attr
                output.addAttribute(new Attribute(attr.getName(), values));
            } else {
                //other attr V() <= T(R)
                output.addAttribute(new Attribute(attr.getName(), Math.min(maxT, attr.getValueCount())));
            }
        }


        // 3. set output
        op.setOutput(output);

        //Add to cost
        // cost =+ output.size
        cost += output.getTupleCount();;

    }
}