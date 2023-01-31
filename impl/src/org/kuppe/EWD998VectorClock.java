package org.kuppe;

import java.util.HashMap;
import java.util.Map;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.reflect.TypeToken;

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
		// De-serialize.
		final TypeToken<Map<String, Integer>> typeToken = new TypeToken<Map<String, Integer>>() { };
		final Map<String, Integer> m = new Gson().fromJson(json, typeToken.getType());
		
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
		for (int i = 0; i < m.size(); i++) {
			this.vc[i] = Math.max(this.vc[i], m.get(Integer.toString(i)));
		}		
	}

	public JsonElement toJson() {
		Map<String, Integer> m = new HashMap<>();
		for (int i = 0; i < vc.length; i++) {
			m.put(Integer.toString(i), vc[i]);
		}
		return new Gson().toJsonTree(m);
	}
}
