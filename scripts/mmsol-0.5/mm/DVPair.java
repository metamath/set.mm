package mm;

final class DVPair {
    public short first, second;

    public DVPair() { first=second=0; }

    public DVPair(short a, short b) throws DVViolation {
	if(a==b) throw new DVViolation(a);
	if(a<b) { first=a; second=b; }
	else { first=b; second=a; }
    }

    public DVPair(DVPair that) { this.first=that.first; this.second=that.second; }

    public boolean equals(Object o) {
	return o!=null && o.getClass()==getClass() && ((DVPair)o).first==first && ((DVPair)o).second==second;
    }

    public boolean hasVar(short v) { return first==v || second==v; }

    public DVPair subst(short v, short sbVar) throws DVViolation {
	if(v==first) return new DVPair(sbVar,second);
	else if(v==second) { return new DVPair(first,sbVar); }
	return new DVPair(this);
    }

    public String toString() { return "DV:<" + first + "," + second + ">"; }
}
