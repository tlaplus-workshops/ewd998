package org.kuppe;

public class EWD998VectorClock {

	private final int[][] vc;
	private final int dimension;
	// This node's id.
	private final int n;

	public EWD998VectorClock(final int n, final int dimension) {
		this.vc = new int[dimension][dimension];
		this.dimension = dimension;
		this.n = n;
	}

	public EWD998VectorClock tick() {
		// /\ clock' = [ clock EXCEPT ![n][n] = @ + 1 ]
		this.vc[n][n]++;
		return this;
	}

	public void merge(final String str) {

		// for a clock of two nodes: id;1;2;3;4
		final String[] split = str.split(";");
		assert split.length == 1 + dimension * dimension;

		final int j = Integer.parseInt(split[0]);
		// in is inbox[n][j].vc below.
		final int[][] in = deserialize(split);

		/*
		 * \* This is where the "magic" of the vector clock happens. /\ LET Max(a,b) ==
		 * IF a < b THEN b ELSE a Merge(r, l) == [ m \in Node |-> IF m = n THEN l[m] + 1
		 * ELSE Max(r[m], l[m]) ] IN clock' = [ clock EXCEPT ![n] =
		 * Merge(inbox[n][j].vc, @) ]
		 */
		this.vc[n][j] = Math.max(this.vc[n][j], in[n][j]);
	}

	private int[][] deserialize(final String[] str) {

		// TODO Dimension could be part of the serialized representation.
		int[][] arr = new int[dimension][dimension];
		int idx = 1;
		for (int i = 0; i < dimension; i++) {
			for (int j = 0; j < arr.length; j++) {
				arr[i][j] = Integer.parseInt(str[idx++]);
			}
		}
		return arr;
	}

	public String serialize() {
		String str = Integer.toString(n) + ";";
		for (int i = 0; i < vc.length; i++) {
			for (int j = 0; j < vc.length; j++) {
				str += Integer.toString(vc[i][j]);
				str += ";";
			}
		}
		return str;
	}
}
