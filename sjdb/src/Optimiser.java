//package sjdb;

import java.util.*;

/**
 * Implement of PlanVisitor
 * Optimise query tree using Heuristic approach
 * (canonical tree -> move select down -> reorder join -> create join -> move project down)
 * Use these steps:
 * Step1. Implement visit() for all kinds of operator, to
 * save all scan（scanList）& save all predicate（predicateSet）& save all attributes.
 * Step2. Push down predicate & attrKept to SCAN，build subTree, and
 * get subTreeList converted from scanList
 * Step3: Reorder subTreeList based on their cost
 * Step4: Connect subTreeList to a planTree using Product
 * Step5. Push down predicate & attrKept to Product, and
 * replace Product with Join (or op-chain)
 */
public class Optimiser implements PlanVisitor {
    private Catalogue catalogue;

    // All scan in origin tree
    List<Scan> scanList = new ArrayList<>();

    // All predicate in origin tree (from Select)
    Set<Predicate> predicateSet = new HashSet<>();//use Set to prevent repeating predicate
    //List<Predicate> predicateList = new ArrayList<>();

    // Attributes needed in the final output
    List<Attribute> attrFinalList = new ArrayList<>();
    //Need Repeat to record how many time does the attr appears in predicates, don't change to set!

    // Attributes needed for predicate ONLY
    Set<Attribute> attrPredList = new HashSet<>();


    /**
     * Pair<Operator subTree, int cost>
     * Help class for Step2, Step3, Step4
     */
    private static class Pair {
        private final Operator subTree;// (root op of) subTree
        private final int cost;//cost of subTree

        public Pair(Operator subTree, int cost) {
            this.subTree = subTree;
            this.cost = cost;
        }

        public Operator getSubTree() {
            return subTree;
        }

        public int getCost() {
            return cost;
        }
    }

    Optimiser(Catalogue catalogue) {
        //To fit Test
        this.catalogue = catalogue;
    }


    // Step1. Implement visit() for all kinds of operator, to
    // save all scan（scanList）& save all predicate（predicateSet）& save all attributes.

    /**
     * Scan: Save (new) scan in scanList
     */
    public void visit(Scan op) {
        scanList.add(new Scan((NamedRelation) op.getRelation()));
    }

    /**
     * Select: Save predicate in predicateSet, Save attr(s) in attrPredList
     */
    public void visit(Select op) {
        predicateSet.add(op.getPredicate());
        if (op.getPredicate().equalsValue()) {
            attrPredList.add(op.getPredicate().getLeftAttribute());
        } else {
            attrPredList.add(op.getPredicate().getLeftAttribute());
            attrPredList.add(op.getPredicate().getRightAttribute());
        }
    }

    /**
     * Project: Save attrs in attrKeptSet
     */
    public void visit(Project op) {
        //PineAlertXX if no final project this will fail, so move to optimiser()
        // and get it directly from the final output of the cononical tree
        //attrFinalList.addAll(op.getAttributes());
    }

    /**
     * Do nothing for Product
     */
    public void visit(Product op) {
        //do nothing
    }

    /**
     * Do nothing for Join
     */
    public void visit(Join op) {
        //do nothing
    }


    /**
     * Return if relation contain the attr(s) that predicate need
     * Help Function for Step2
     *
     * @return boolean
     */
    boolean isRelationContainPred(Relation relation, Predicate pred) {
        if (pred.equalsValue()) {
            //attr = value
            Attribute attrKept = pred.getLeftAttribute();
            try {
                //find successfully
                relation.getAttribute(attrKept);
                return true;
            } catch (Exception e) {
                //can't find
                return false;
            }
        } else {
            //attr = attr
            Attribute attrKeptLeft = pred.getLeftAttribute();
            Attribute attrKeptRight = pred.getRightAttribute();
            try {
                //find successfully
                relation.getAttribute(attrKeptLeft);
                relation.getAttribute(attrKeptRight);
                return true;
            } catch (Exception e) {
                //can't find
                return false;
            }
        }
    }

    /**
     * Connect subTreeList using Product ([0] at bottom, [n] at top)
     * Return rootOp of reconnected tree
     * Help function for Step4
     * ALERT: CHANGE the restSubTreeList of Caller
     */
    Product reConnect(List<Pair> restSubTreeList) {
        // (Recursion)
        if (restSubTreeList.size() <= 2) {
            //base case, when meet the two bottom leaf
            return new Product(restSubTreeList.get(0).getSubTree(),
                    restSubTreeList.get(1).getSubTree()); //(left, right)
        } else {
            //process
            Operator lastSubTree = restSubTreeList.get(restSubTreeList.size() - 1).getSubTree();
            restSubTreeList.remove(restSubTreeList.size() - 1);
            return new Product(reConnect(restSubTreeList), lastSubTree);//(left, right)
        }
    }

    /**
     * Push down predicate and attrKept
     * To create Join(or may be op-chain like Project-Select-Join) to replace Product
     * Return the rootOp of new tree
     * Help function for Step5
     *
     * @return Operator: rootOp of new tree
     */
    Operator createJoin(Operator op) {
        //(Recursion) create Join (or op-chain) to replace Product
        if (!(op instanceof Product)) {
            //base case, meet the two bottom leaf
            return op;
        } else {
            //process, op is Product
            // Change (create join) the left input op with recursion
            Relation outputRelation = op.getOutput();
            Operator rootOp = new Product(createJoin(((Product) op).getLeft()),
                    ((Product) op).getRight());

            //move down predicates, create Join or Select (delete used predicate)
            Iterator<Predicate> itPred = predicateSet.iterator();
            while (itPred.hasNext()) {
                Predicate pred = itPred.next();
                if (isRelationContainPred(outputRelation, pred)) {
                    if (rootOp instanceof Product) {
                        // rootOp is still a Product
                        // which means Product haven't been replaced by Join
                        // (or be added a parent select)
                        // which means Join haven't been created in this op-chain
                        // Replace Product with Join

                        //create output
                        Estimator estimator = new Estimator();
                        rootOp.accept(estimator);
                        if (!pred.equalsValue()) {
                            //PineAlertXX because of join reorder, pred(a=a)may need to be reverse
                            try {
                                //no reorder
                                ((Product) rootOp).getRight().getOutput().getAttribute(pred.getRightAttribute());
                                ((Product) rootOp).getLeft().getOutput().getAttribute(pred.getLeftAttribute());
                            } catch (Exception e) {
                                //need reorder
                                pred = new Predicate(pred.getRightAttribute(),
                                        pred.getLeftAttribute());
                            }
                        }
                        rootOp = new Join(
                                ((Product) rootOp).getLeft(), ((Product) rootOp).getRight(), pred);
                    } else {
                        rootOp = new Select(rootOp, pred);
                    }
                    // delete used attr pred in attrPredList, so
                    // the projection of this op-chain keep only attr necessary for future BinaryOp
                    if (pred.equalsValue()) {
                        attrPredList.remove(pred.getLeftAttribute());
                    } else {
                        attrPredList.remove(pred.getLeftAttribute());
                        attrPredList.remove(pred.getRightAttribute());
                    }
                    itPred.remove();
                }
            }

            //move down attrFinal and attrPred(delete used), create projection
            Set<Attribute> projectAttrSet = new HashSet<>();// prevent repeating attr
            for (Attribute attrFinal : attrFinalList) {
                try {
                    Attribute attr = outputRelation.getAttribute(attrFinal);
                    projectAttrSet.add(attr);
                } catch (Exception e) {
                    // can't find, do nothing;
                }
            }
            for (Attribute attrPred : attrPredList) {
                try {
                    Attribute attr = outputRelation.getAttribute(attrPred);
                    projectAttrSet.add(attr);
                } catch (Exception e) {
                    // can't find, do nothing;
                }
            }
            List<Attribute> projectAttrList = new ArrayList<>(projectAttrSet);
            if (projectAttrList.size() != outputRelation.getAttributes().size()) {
                rootOp = new Project(rootOp, projectAttrList);
            }// if ==, project all, omit project
            return rootOp;
        }
    }


    public Operator optimise(Operator plan) {
        // for reuse, clear
        scanList.clear();
        predicateSet.clear();
        attrFinalList.clear();
        attrPredList.clear();

        // get origin tree data
        plan.accept(this);
        attrFinalList.addAll(plan.getOutput().getAttributes());

        // Step2. Push down predicate & attrKept to SCAN，build subTree, and
        // Get subTreeList converted from scanList
        List<Pair> subTreeList = new ArrayList<>();//<subTreeRootOp, subTreeCost>
        for (Scan oneScan : scanList) {
            Relation inputRelation = oneScan.getRelation();
            Operator rootOp = oneScan;

            // 2.1 move down predicates, create select (delete used predicate)
            Iterator<Predicate> itPred = predicateSet.iterator();
            while (itPred.hasNext()) {
                Predicate pred = itPred.next();
                if (isRelationContainPred(inputRelation, pred)) {
                    rootOp = new Select(rootOp, pred);
                    if (pred.equalsValue()) {
                        attrPredList.remove(pred.getLeftAttribute());
                    } else {
                        attrPredList.remove(pred.getLeftAttribute());
                        attrPredList.remove(pred.getRightAttribute());
                    }
                    itPred.remove();
                }
            }


            //move down attrFinal and attrPred(delete used), create projection
            Set<Attribute> projectAttrSet = new HashSet<>();// prevent repeating attr
            for (Attribute attrFinal : attrFinalList) {
                try {
                    Attribute attr = inputRelation.getAttribute(attrFinal);
                    projectAttrSet.add(attr);
                } catch (Exception e) {
                    // can't find, do nothing;
                }
            }
            for (Attribute attrPred : attrPredList) {
                try {
                    Attribute attr = inputRelation.getAttribute(attrPred);
                    projectAttrSet.add(attr);
                } catch (Exception e) {
                    // can't find, do nothing;
                }
            }
            if (projectAttrSet.size() == 0) {
                //No attr in this scan(subTree) needed to be kept, so not save it to subTreeList
                continue;
            }
            List<Attribute> projectAttrList = new ArrayList<>(projectAttrSet);
            if (projectAttrList.size() != inputRelation.getAttributes().size()) {
                rootOp = new Project(rootOp, projectAttrList);
            }// if ==, project all, omit project


            // 2.3 Calculate cost of each subTree for future reorder (Step3)
            Estimator estimator = new Estimator();
            rootOp.accept(estimator);
            int cost = estimator.cost;
            subTreeList.add(new Pair(rootOp, cost));
        }

        // Edge Case: only scan one relation, no BinaryOp in canonical tree
        // no need to connect or else
        if (scanList.size() == 1) {
            return subTreeList.get(0).getSubTree();
        }

        // Step3: Reorder subTreeList based on their cost
        // ([0]: cost min, will be put at bottom of tree later)
        // ([1]: cost max, will be put at top of tree later)
        subTreeList.sort(Comparator.comparing(Pair::getCost));

        // Step4: Connect subTreeList to a planTree using Product
        // ([0] at bottom, [n] at top)
        Product rootProd = reConnect(subTreeList);
        // Build relation for every op
        Estimator estimator = new Estimator();
        rootProd.accept(estimator);
        // clean up cost for next usage
        estimator.cost = 0;

        // Step5. Push down predicate & attrFinal & attrPred to Product, and
        // replace Product with Join (or op-chain)
        Operator rootJoin = createJoin(rootProd);
        rootJoin.accept(estimator);
        // clean up cost for next usage
        estimator.cost = 0;

        return rootJoin;
    }

    /*
    //How to safely delete element of the list that are being looped
    Iterator<Type> iterator = list.iterator();
    while(iterator.hasNext()) {
        Type element = iterator.next();
        if () {
            iterator.remove();
        }
    }
     */


}