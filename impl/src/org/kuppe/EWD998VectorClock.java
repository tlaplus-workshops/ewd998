package org.kuppe;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

public class EWD998VectorClock {

	private final int[] vc;
	// This node's id.
	private final int n;

	public EWD998VectorClock(final int n, final int dimension) {
		this.vc = new int[dimension];
		this.n = n;
	}

	public EWD998VectorClock tick() {
		// /\ clock' = [ clock EXCEPT ![n][n] = @ + 1 ]
		this.vc[n]++;
		return this;
	}

	public void merge(final JsonObject json) {
		/*
		 * This is where the "magic" of the vector clock happens. 
		 * 
		 * /\ LET Max(a,b) == IF a < b THEN b ELSE a
		 *  
		 *        Merge(r, l) == [ m \in Node |-> IF m = n THEN l[m] + 1
		 *                                    ELSE Max(r[m], l[m]) ]
		 *                                    
		 *    IN clock' = [ clock EXCEPT ![n] = Merge(inbox[n][j].vc, @) ]
		 */
		final JsonArray arr = json.get("clock").getAsJsonArray();
		for (int i = 0; i < vc.length; i++) {
			this.vc[i] = Math.max(this.vc[i], arr.get(i).getAsInt());
		}
	}

	public JsonElement toJson() {
		final JsonObject result = new JsonObject();
		result.add("id", new JsonPrimitive(n));
		
		final JsonArray arr = new JsonArray(vc.length);
		for (int i = 0; i < vc.length; i++) {
			arr.add(vc[i]);
		}
		result.add("clock", arr);

		return result;
	}
}
