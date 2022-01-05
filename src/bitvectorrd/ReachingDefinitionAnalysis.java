
package bitvectorrd;

import soot.jimple.DefinitionStmt;
import java.util.*;
import java.util.ArrayList;
import java.util.Map;
import java.util.Iterator;
import java.util.List;
import soot.Value;

import soot.toolkits.graph.UnitGraph;
import soot.Body;
import soot.Local;
import soot.Unit;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.Stmt;
import soot.tagkit.LineNumberTag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

import soot.toolkits.scalar.FlowSet;
import soot.toolkits.scalar.AbstractFlowSet;
import soot.toolkits.scalar.ArraySparseSet;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import soot.toolkits.scalar.Pair;
import soot.util.Chain;
import soot.JimpleBodyPack;
import soot.jimple.DefinitionStmt;
import java.util.Arrays;
import java.util.*;

public class ReachingDefinitionAnalysis extends ForwardFlowAnalysis {

    Body body;
    FlowSet inval, outval;
    FlowSet merge_result;
    int flag1=0;

    public ReachingDefinitionAnalysis(UnitGraph g) {
        super(g);
        body = g.getBody();
        Chain<Local> local_variables = body.getLocals();
        ArrayList<String> arr = new ArrayList<String>();
        for (Local str : local_variables) {
        	arr.add(str.toString());
        }
        System.out.println("local variables: "+arr);
        doAnalysis();
        Iterator iter = outval.iterator();
        if(iter.hasNext()) {
        	System.out.println("result");
	        while (iter.hasNext()) {
	            Pair pair = (Pair<String, String>) iter.next();
	            if( pair.getO1().toString().charAt(0)=='#') {
	            	System.out.println("[" + pair.getO1().toString().substring(1, pair.getO1().toString().length()) + "," + pair.getO2().toString() + "]");
	            }
	            else {
	            	System.out.println("[" + pair.getO1().toString() + "," + pair.getO2().toString() + "]");
	            }
	        }
        }
    }
    
    
    @Override
    protected void flowThrough(Object in, Object unit, Object out) {
        inval = (FlowSet) in;
        outval = (FlowSet) out;
        List<String> rhs_array = new ArrayList<String>();
        Stmt u = (Stmt) unit;
        System.out.println("Statement: " + u);
        if(flag1 == 1) {
        	inval=merge_result;
        	flag1=0;
        }
        inval.copy(outval);
        String var;
       
        if(u instanceof AssignStmt || u instanceof IdentityStmt ) { 
	        System.out.println("\nInSet: ");
	        Iterator iter = inval.iterator();
	        while (iter.hasNext()) {
	            Pair pair = (Pair<String, String>) iter.next();
	            System.out.print("[" + pair.getO1().toString() + ", " + pair.getO2().toString() + "]  ");
	        }
	        System.out.println('\n');
        }
	        
      //Kill the var which is defined
        String kill_var_sign="";
        if (u instanceof AssignStmt) {
            Iterator<ValueBox> defIt = u.getDefBoxes().iterator();
            ArrayList<Pair<String, String>> to_kill = new ArrayList<Pair<String, String>>();
            if(defIt.hasNext()) {
            	String definedVar = defIt.next().getValue().toString();
            	Iterator itOut = outval.iterator();
                while (itOut.hasNext()) {
                    Pair pair = (Pair<String, String>) itOut.next();
                    String str1 = pair.getO1().toString();
                    if(str1.charAt(0) != '#' && pair.getO1().toString().equals(definedVar)) {	          
                    	System.out.println("pair to be killed: "+pair.getO1().toString()+ ',' +pair.getO2().toString());
                    	kill_var_sign=pair.getO2().toString();
                        to_kill.add(pair);	                    
                    }
                }
            }
            Iterator<Pair<String, String>> pIt = to_kill.iterator();
            while (pIt.hasNext()) {
            	Pair<String, String> p = pIt.next();
            	outval.remove(p);
            	System.out.println("After Killing" + outval);
            }
        }
        //Gen the variable which is defined
        if(u instanceof AssignStmt) {
    		Value rhs = ((AssignStmt) u).getRightOp();
    		Value lhs = ((AssignStmt) u).getLeftOp();
    		String rhs_string=rhs.toString();
    		
    		//----------------------Creating array of operators and operands ------------------
    		char[] operators=new char[] {'[','+', '-', '*', '/'};
    		//--------Bin_exp 0 is for unary expressions and Bin_exp 1 is for binary expressions---------------
    		int Bin_exp=0,i=0;
			String str1="";
			if(rhs_string.charAt(0) == '-') {
				i=1;
			}
			else if(rhs_string.indexOf("neg")==0) {
				i=4;
			}
			if(rhs_string.charAt(0) == '-' || rhs_string.indexOf("neg")==0) {
				str1="-";
				while(i<rhs_string.length() && rhs_string.charAt(i) != ' ') {
    				for(char op: operators) {
    					if(rhs_string.charAt(i) == op) {
    						Bin_exp=1;
    						break;
    					}
    				}
    				if(Bin_exp==1) break;
    				str1+=rhs_string.charAt(i);
    				i+=1;
				}
			}
			else
			{
				while(i<rhs_string.length()) {
					for(char op: operators) {
						if(rhs_string.charAt(i) == op) {
							Bin_exp=1;
							break;
						}
					}
					if(Bin_exp==1) break;
					str1+=rhs_string.charAt(i);
					i+=1;
				}
			}
			if(Bin_exp == 0) {
				rhs_array.add(str1);
			}
			else {
				rhs_array = Arrays.asList(rhs_string.split(" ", 0));
			}
    		
    		
    		//-----------------------------------------------------------------------------------------
    		
    		// ------- Unary Expressions ---------------
			
    		if(rhs_array.size() == 1) {
    			
    			String resultant_sign = "";
    			//---------RHS like y=500 ------------
    			if(rhs_array.get(0).charAt(0) > '0' && rhs_array.get(0).charAt(0) <= '9'){
    				resultant_sign = "+";
    			}
    			
    			//---------RHS like y= arr[r]------------
    			else if(rhs_array.get(0).charAt(rhs_array.get(0).length()-1) == ']') {
    				resultant_sign = "T";
    			}
    			
    			//---------RHS like y=0 ------------
    			else if(rhs_array.get(0).charAt(0) == '0') {
    				resultant_sign = "0";
    			}
    			
    			else if(rhs_array.get(0).charAt(0) == '-') {
    				
    				//---------RHS like y=-x ------------
    				if(rhs_array.get(0).charAt(1)<'0' || rhs_array.get(0).charAt(1)>'9') {
    					Iterator it1 = inval.iterator();
        		        while (it1.hasNext()) {
        		            Pair pair = (Pair<String, String>) it1.next();
        		            String operand = rhs_array.get(0).substring(1, rhs_array.get(0).length());
        		            //--------- invert the sign------------
        		            if(pair.getO1().toString().equals(operand)) {        		           
        		            	if(pair.getO2().toString() == "-") {
        		            		resultant_sign = "+";
        		            	}
        		            	else {
        		            		resultant_sign = "-";
        		            	}
        		           }
        		        }
        			}
    				
    				//---------RHS like y=-500 ------------
    				else {
    					resultant_sign = "-";}
    			}
    			//---------RHS like y=x------------
    			else {
    				Iterator it1 = inval.iterator();
    		        while (it1.hasNext()) {
    		            Pair pair = (Pair<String, String>) it1.next();
    		            if(pair.getO1().toString().equals(rhs_array.get(0))) {
    		            	resultant_sign = pair.getO2().toString();
    		            }
    		        }
    			}
    			Pair pair = new Pair(lhs, resultant_sign);
				outval.add(pair);				
				System.out.println("Generating " + pair.getO1() + "," + pair.getO2());
    		}
    		
    		//------------- Binary expressions ------------
    		else if(rhs_array.size() == 3) {
    			String resultant_sign="";
    			String operator=rhs_array.get(1); 
    			String first_operand=rhs_array.get(0);
    			String second_operand=rhs_array.get(2);
    			
    			
    			//-------------------- working on the first operand----------------
    			String sign1="";
    			Iterator it1 = inval.iterator();
    			// operand is a number
    			if(first_operand.charAt(0) > '0' && first_operand.charAt(0) <= '9'){
    	    		sign1 = "+";
    	    	}
    			// operand is a negative number
    	    	else if(first_operand.charAt(0) == '-'){
    	    		sign1 = "-";
    	    	}
    	    	// operand is 0
    	    	else if(first_operand.charAt(0) == '0'){
    	    		sign1 = "0";
    	    	}
    			// operand is a variable
    			if((first_operand.charAt(0) < '0' || first_operand.charAt(0) > '9') && first_operand.charAt(0) != '-') {
    	    		while (it1.hasNext()) {
    					Pair pair = (Pair<String, String>) it1.next();
    		        	if(pair.getO1().toString().equals(first_operand)) {
    		        		sign1 = pair.getO2().toString();
    		        	}    
    		        }
    	    	}
    	    	
    	    	
    	    	
    	    	//-------------------- working on the second operand----------------  	
    	    	String sign2="";
    	    	Iterator it2 = inval.iterator();
    			// operand is a variable
    	    	if((second_operand.charAt(0) < '0' || second_operand.charAt(0) > '9') && second_operand.charAt(0) != '-') {
    	    		while (it2.hasNext()) {
    					Pair inv2 = (Pair<String, String>) it2.next();
    		        	if(inv2.getO1().toString().equals(second_operand)) {
    		        		sign2 = inv2.getO2().toString();
    		        	}    
    		        }
    	    	}
    	    	// operand is a number
    	    	else if(second_operand.charAt(0) > '0' && second_operand.charAt(0) <= '9'){
    	    		sign2 = "+";
    	    	}
    	    	// operand is a negative number
    	    	else if(second_operand.charAt(0) == '-'){
    	    		sign2 = "-";
    	    	}
    	    	// operand is 0
    	    	else if(second_operand.charAt(0) == '0'){
    	    		sign2 = "0";
    	    	}
    	    	
    	    	
    	    	// cases where lhs variable is used in rhs 
    	    	if(first_operand.equals(lhs.toString())) {
					sign1=kill_var_sign;
				}
				else if(second_operand.equals(lhs.toString())) {
					sign2=kill_var_sign;
				}
    	    	
    	    	// --------------comparing the operands's signs and using the operator to assign the new sign ------------------
    	    	//operator is addition
    	    	if(operator.equals("+")) {
    	    		if(sign1.equals("b") || sign2.equals("b")) {
    	    			resultant_sign = "b";
    	        	}
    	    		else if(sign1.equals("T") || sign2.equals("T")) {
    	        		resultant_sign = "T";
    	        	}
    	    		else if(sign2.equals("0")) {
    	        		resultant_sign = sign1;
    	        	}
    	        	else if(sign1.equals("0")) {
    	        		resultant_sign = sign2;
    	        	}
    	        	else if(sign1.equals("+") && sign2.equals("+")) {
    	        		resultant_sign = "+";
    	        	}
    	        	else if(sign1.equals("-") && sign2.equals("-")) {
    	        		resultant_sign = "-";
    	        	}
    	        	else {
    	        		resultant_sign = "T";
    	        	}
    			}
    	    	
    	    	// operator is subtraction
    			else if(operator.equals("-")) {
    				if(sign1.equals("b") || sign2.equals("b")) {
    					resultant_sign = "b"; 
    		    	}
    		    	else if(sign1.equals("T") || sign2.equals("T")) {
    		    		resultant_sign = "T";
    		    	}
    		    	else if((sign1.equals("+") && sign2.equals("+"))|| (sign1.equals("-") && sign2.equals("-"))) {
    		    		resultant_sign = "T";
    		    	}
    		    	else if(sign1.equals("+") || (sign1.equals("0") && sign2.equals("-"))) {
    		    		resultant_sign = "+";
    		    	}
    		    	else if(sign2.equals("+") ||(sign1.equals("-") && sign2.equals("0"))) {
    		    		resultant_sign = "-";
    		    	}
    		    	else if(sign1.equals("0") && sign2.equals("0")) {
    		    		resultant_sign = "0";
    		    	}
    		   	}

    	    	// operator is multiplication
    			else if(operator.equals("*")) {
    				if(sign1.equals("b") || sign2.equals("b")) {
    					resultant_sign = "b";
    		    	}
    		    	else if(sign1.equals("0") || sign2.equals("0")) {
    		    		resultant_sign = "0";
    		    	}
    		    	else if(sign1.equals("T") || sign2.equals("T")) {
    		    		resultant_sign = "T";
    		    	}
    		    	else if((sign1.equals("+") && sign2.equals("-"))|| (sign1.equals("-") && sign2.equals("+"))) {
    		    		resultant_sign = "-";
    		    	}
    		    	else {
    		    		resultant_sign = "+";
    		    	}
    			}
    	    	
    	    	// operator is division
    			else if(operator.equals("/")) {
    				if(sign1.equals("b") || sign2.equals("b") || sign2.equals("0")) {
    					resultant_sign = "b";
    		    	}
    		    	else if((sign2.equals("-") || sign2.equals("+")) && sign1.equals("0")) {
    		    		resultant_sign = "0";
    		    	}
    		    	else {
    		    		resultant_sign = "T";
    		    	}
    			}
    			Pair pair = new Pair(lhs, resultant_sign);
				outval.add(pair);
				System.out.println("Generating " + pair.getO1() + "," + pair.getO2());
    		}
        }
        
      //--------------------Printing the outset--------------------------
        if(u instanceof AssignStmt || u instanceof IdentityStmt) {
	        System.out.println("\nOutset: ");
	        Iterator itOut = outval.iterator();
	        while (itOut.hasNext()) {
	            Pair inv = (Pair<String, String>) itOut.next();
	            System.out.print("[" + inv.getO1().toString() + ", " + inv.getO2().toString() + "]  ");
	        }
	        System.out.println();
        }
    }

    @Override
    protected void copy(Object source, Object dest) {
        FlowSet srcSet = (FlowSet) source;
        FlowSet destSet = (FlowSet) dest;
        srcSet.copy(destSet);
        Iterator it = destSet.iterator();
    }

    @Override
    protected Object entryInitialFlow() {
        ArraySparseSet arr = new ArraySparseSet();
        Chain<Local> local_variables = this.body.getMethod().getActiveBody().getLocals();
        Iterator<Local> i2 = local_variables.iterator();
        while (i2.hasNext()) {
            Local local = i2.next();
            String str = local.getName();
            if(local.getType().toString()!="int" && local.getType().toString()!="byte") {
            	str = "#" + str;
            	Pair<String, String> p = new Pair<String, String>(str, "b");
            	arr.add(p);
                System.out.println("Initial pairs: " + p);
            }
            else if (!((str.equals("this")))) {
	                Pair<String, String> p = new Pair<String, String>(str, "T");
	                arr.add(p);
	                System.out.println("Initial pairs: " + p);
	        }
        }
        return arr;
    }

    @Override
    protected void merge(Object in1, Object in2, Object out) {
    	FlowSet inval1 = (FlowSet) in1;
    	FlowSet inval2 = (FlowSet) in2;
    	FlowSet outSet = (FlowSet) out;
    	flag1=1;
    	
    	ArraySparseSet array_final = new ArraySparseSet();
    	Dictionary dict = new Hashtable();
    	Iterator iter = inval1.iterator();
    	
    	
        while (iter.hasNext()) {
            Pair pair = (Pair<String, String>) iter.next();
            dict.put(pair.getO1().toString(), pair.getO2().toString());
        }
        Iterator iter1 = inval2.iterator();
        if(!iter1.hasNext()) {
        	iter = inval1.iterator();
        	while(iter.hasNext()) {
        		Pair pair = (Pair<String, String>) iter.next();
        		array_final.add(pair);
        	}
        }
        else {
	        while (iter1.hasNext()) {
	            Pair pair = (Pair<String, String>) iter1.next();
	            if(dict.get(pair.getO1().toString()).equals(pair.getO2().toString())) {
	            	Pair<String, String> pair1 = new Pair<String, String>(pair.getO1().toString(), pair.getO2().toString());
	            	array_final.add(pair1);
	            }
	            else {
	            	Pair<String, String> pair1 = new Pair<String, String>(pair.getO1().toString(), "T");
	            	array_final.add(pair1);
	            }
	        }
        }
        outSet = (FlowSet) array_final;
        merge_result = outSet;
    }

    @Override
    protected Object newInitialFlow() {
        ArraySparseSet as = new ArraySparseSet();
        return as;
    }

}

