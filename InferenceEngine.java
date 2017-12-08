import java.io.*;
import java.util.*;
class Predicate{
    class st{
        String str;
        ArrayList<String> var;
        boolean pos;
    }
    ArrayList<st> pre;
    int startFrom(int i,String st){
        for(;i<pre.size();i++)
            if(pre.get(i).str.equals(st))
                return i;
        return -2;
    }
    void negateAll(){
        for(int i=0;i<pre.size();i++)
            pre.get(i).pos =!pre.get(i).pos;
    }
    public Predicate copy() {
        Predicate p=new Predicate();
        p.pre=new ArrayList<>();
        for (st s:pre) {
            Predicate.st stmt=new Predicate.st();
            stmt.str=s.str;
            stmt.pos=s.pos;
            stmt.var=new ArrayList<>();
            for(int i=0;i<s.var.size();i++)
                stmt.var.add(new String(s.var.get(i)));
            p.pre.add(stmt);
        }
        return p;
    }
    Predicate(){
        pre=new ArrayList<>();
    }
    Predicate(String s){
        char c[];
        c=s.toCharArray();
        boolean pos=true,pred=true;
        st stmt=new st();
        pre=new ArrayList<>();
        stmt.var=new ArrayList<>();
        StringBuffer p1=new StringBuffer(),p2=new StringBuffer();
        for(int i=0;i<c.length;i++){
            switch (c[i]){
                case '|':
                case ' ':continue;
                case ')':
                    pred=true;
                    stmt.pos=pos;
                    stmt.var.add(p2.toString());
                    p2=new StringBuffer();
                    pos=true;
                    stmt.str=p1.toString();
                    pre.add(stmt);
                    stmt=new st();
                    p1=new StringBuffer();break;
                case ',':
                    stmt.var.add(p2.toString());
                    p2=new StringBuffer();
                    break;
                case '(':stmt.var=new ArrayList<>();pred=false;break;
                case '~':pos=false;break;
                default:
                    if(pred)
                        p1.append(c[i]);
                    else
                        p2.append(c[i]);
            }
        }
    }
}
class KB {
    ArrayList<Predicate> kb;
    HashMap<String, ArrayList<Integer>> kbp;
    ArrayList<Predicate> pre;
    KB() {
        kb = new ArrayList<>();
        kb.add(new Predicate());
    }
    void addIndex() {
        Predicate.st s = kb.get(kb.size() - 1).pre.get(0);
        int index = kb.size()-1;
        if (!s.pos)
            index = -index;
        if(kbp.containsKey(s.str))
            kbp.get(s.str).add(index);
    }
    void remove(int i) {
        for (String str : kbp.keySet()) {
            ArrayList<Integer> ai = kbp.get(str);
            for (int j = 0; j < ai.size(); j++)
                if (ai.get(j) == i||ai.get(j)==-i) {
                    ai.remove(j);
                    j--;
                }
        }
    }
    void add(Predicate p) {
        kb.add(p);
    }
    void tabulate() {
        ListIterator<Predicate> it = kb.listIterator();
        kbp = new HashMap<>();
        it.next();
        while (it.hasNext()) {
            int index = it.nextIndex();
            Predicate p = it.next();
            for (Predicate.st key : p.pre) {
                boolean pos = key.pos;
                if (kbp.containsKey(key.str))
                    kbp.get(key.str).add((pos) ? index : -index);
                else {
                    ArrayList<Integer> ai = new ArrayList<>();
                    ai.add((pos) ? index : -index);
                    kbp.put(key.str, ai);
                }
            }
        }
    }
    boolean validate(Predicate p) throws Exception {
        if (p.pre.size() == 0)
            return true;
        if(KbContains(p.copy()))
            return false;
        pre.add(p.copy());
        int i=-1,j;
        for(Predicate.st pr: p.pre){
            ++i;
            ArrayList<Integer> pl=null;
            if(kbp.containsKey(pr.str))
                pl=kbp.get(pr.str);
            if(pl!=null)
                for (Integer kbl:pl) {
                    j=-1;
                    if((kbl<0&&!pr.pos)||(kbl>0&&pr.pos))
                        continue;
                    kbl=(kbl>0)?kbl:-kbl;
                    Predicate q=kb.get(kbl);
                    while(true){
                        j=q.startFrom(++j,p.pre.get(i).str);
                        if(j<0)
                            break;
                        Predicate Tp=p.copy(),Tq=q.copy();
                        if(canUnify(Tp,Tq,i,j)){
                            Predicate k=unify(Tp,Tq,i,j);
                            if(k==null)
                                continue;
                            boolean stat =validate(k);
                            if(stat)
                                return stat;
                        }
                    }
                }
        }
        return false;
    }
    boolean samekb(Predicate q,Predicate p) {
        for(int i=0;i<p.pre.size();i++){
            if(isFound(p,q,i,0)){
                Predicate tp=p.copy(),tq=q.copy();
                tp.pre.remove(i);
                tq.pre.remove(0);
                if(tq.pre.size()==0)
                    return true;
                if(samekb(tq,tp))
                    return true;
            }
        }
        return false;
    }
    Boolean KbContains(Predicate p){
        p.negateAll();
        for(Predicate q:pre) {
            if (samekb(q.copy(), p.copy()))
                return true;
        }
        return false;
    }
    boolean isConstant(String s) {
        return Character.isUpperCase(s.charAt(0));
    }
    boolean isFound(Predicate p,Predicate q,int i,int j){
        if(!p.pre.get(i).str.equals(q.pre.get(j).str))
            return  false;
        if(p.pre.get(i).pos==q.pre.get(j).pos)
            return false;
        if(p.pre.get(i).var.size()!=q.pre.get(j).var.size())
            return false;
        for (int y = 0; y < p.pre.size(); y++)
            for (int z = 0; z < p.pre.get(y).var.size(); z++)
                if (!isConstant(p.pre.get(y).var.get(z)))
                    p.pre.get(y).var.set(z,p.pre.get(y).var.get(z)+'^');
        HashMap<String,String> hm=new HashMap<>();
        for(int x=0;x<p.pre.get(i).var.size();x++) {
            if (isConstant(p.pre.get(i).var.get(x)) && isConstant(q.pre.get(j).var.get(x)) && !p.pre.get(i).var.get(x).equals(q.pre.get(j).var.get(x)))
                return false;
            if(isConstant(p.pre.get(i).var.get(x)) && isConstant(q.pre.get(j).var.get(x)))
                continue;
            if(isConstant(p.pre.get(i).var.get(x)) || isConstant(q.pre.get(j).var.get(x)) )
                return false;
            if(p.pre.get(i).var.get(x).equals(q.pre.get(j).var.get(x)))
                continue;
            String st=p.pre.get(i).var.get(x),str=q.pre.get(j).var.get(x);
            if(hm.containsKey(st)&&!hm.get(st).equals(str))
                return false;
            if(hm.containsKey(str)&&!hm.get(str).equals(st))
                return false;
            hm.put(str,st);
            hm.put(st,str);
        }
        return true;
    }
    Predicate unify(Predicate p,Predicate q,int i,int j){
        p.pre.remove(i);
        q.pre.remove(j);
        for(Predicate.st st:q.pre)
            p.pre.add(st);
        return compress(p);
    }
    Predicate compress(Predicate p){
        for(int i=0;i<p.pre.size();i++)
            for(int j=i+1;j<p.pre.size();j++)
                if(p.pre.get(i).str.equals(p.pre.get(j).str)) {
                    if (isSame(p.pre.get(i).var, p.pre.get(j).var)) {
                        if (p.pre.get(i).pos != p.pre.get(j).pos)
                            return null;
                        p.pre.remove(j--);
                    }
                       else if(sameCount(p,p.pre.get(i).var, p.pre.get(j).var,i,j))
                         p.pre.remove(j--);
                }
        return p;
    }
    boolean isSame(ArrayList<String> a,ArrayList<String> b){
        for(int i=0;i<a.size();i++)
            if(!a.get(i).equals(b.get(i)))
                return false;
        return true;
    }
    boolean sameCount(Predicate p, ArrayList<String> a,ArrayList<String> b ,int i,int j){
        if(p.pre.get(i).pos!=p.pre.get(j).pos)
            return  false;
        for(int k=0;k<a.size();k++){
            if(isConstant(a.get(k)))
                if(!isConstant(b.get(k)))
                    return false;
            if(isConstant(b.get(k)))
                if(!isConstant(a.get(k)))
                    return false;
        }
        Set<String> s1=new HashSet<>(),s2=new HashSet<>();
        for(int k=0;k<p.pre.size();k++)
            if(k!=i&&k!=j){
                for (String st:p.pre.get(k).var) {
                    s1.add(st);
                    s2.add(st);
                }
            }
        for (String st:p.pre.get(i).var)
            s1.add(st);
        for (String st:p.pre.get(j).var)
            s2.add(st);
        for(String st: a)
            if(s2.contains(st))
                return false;
        for(String st:b)
            if(s1.contains(st))
                return false;
        for(int k=0;k<a.size();k++){
            for(int l=k+1;l<a.size();l++){
                if(a.get(k).equals(a.get(l)))
                    if(!b.get(k).equals(b.get(l)))
                        return false;
                if(b.get(k).equals(b.get(l)))
                    if(!a.get(k).equals(a.get(l)))
                        return false;
            }
        }
        return true;
    }
    boolean canUnify(Predicate p,Predicate q,int i,int j) {
        if (!p.pre.get(i).str.equals(q.pre.get(j).str))
            return false;
        if (p.pre.get(i).pos == q.pre.get(j).pos)
            return false;
        if (p.pre.get(i).var.size() != q.pre.get(j).var.size())
            return false;
        Set<String> hs1 = new HashSet<>();
        Set<String> hs2 = new HashSet<>();
        HashMap<String, String> hm = new HashMap<>();
        for (int y = 0; y < p.pre.size(); y++)
            for (int z = 0; z < p.pre.get(y).var.size(); z++)
                if (!isConstant(p.pre.get(y).var.get(z)))
                    hs2.add(p.pre.get(y).var.get(z));
        for (int y = 0; y < q.pre.size(); y++)
            for (int z = 0; z < q.pre.get(y).var.size(); z++)
                if (!isConstant(q.pre.get(y).var.get(z)))
                    hs1.add(q.pre.get(y).var.get(z));
        for (int y = 0; y < p.pre.size(); y++)
            for (int z = 0; z < p.pre.get(y).var.size(); z++)
                if (!isConstant(p.pre.get(y).var.get(z)) && hs1.contains(p.pre.get(y).var.get(z))) {
                    if(!hm.containsKey(p.pre.get(y).var.get(z))){
                        StringBuffer st=new StringBuffer(p.pre.get(y).var.get(z));
                        st.append("%");
                        while(hs2.contains(st.toString()))
                            st.append("%");
                        hs2.add(st.toString());
                        hm.put(p.pre.get(y).var.get(z),st.toString());
                    }
                }
        for (int y = 0; y < p.pre.size(); y++)
            for (int z = 0; z < p.pre.get(y).var.size(); z++)
                if(hm.containsKey(p.pre.get(y).var.get(z)))
                    p.pre.get(y).var.set(z,hm.get(p.pre.get(y).var.get(z)));
        for(int x=0;x<p.pre.get(i).var.size();x++) {
            if (isConstant(p.pre.get(i).var.get(x)) && isConstant(q.pre.get(j).var.get(x)) && !p.pre.get(i).var.get(x).equals(q.pre.get(j).var.get(x)))
                return false;
            if (!isConstant(p.pre.get(i).var.get(x)) && !isConstant(q.pre.get(j).var.get(x))){
                String st=p.pre.get(i).var.get(x),str=q.pre.get(j).var.get(x);
                for (int y = 0; y < p.pre.size(); y++)
                    for (int z = 0; z < p.pre.get(y).var.size(); z++)
                        if (p.pre.get(y).var.get(z).equals(st))
                            p.pre.get(y).var.set(z, str);
                for (int y = 0; y < q.pre.size(); y++)
                    for (int z = 0; z < q.pre.get(y).var.size(); z++)
                        if (q.pre.get(y).var.get(z).equals(st))
                            q.pre.get(y).var.set(z, str);
            }
            else  {
                String st,str;
                if (!isConstant(p.pre.get(i).var.get(x))) {
                    st = p.pre.get(i).var.get(x);
                    str = q.pre.get(j).var.get(x);
                }
                else {
                    str = p.pre.get(i).var.get(x);
                    st = q.pre.get(j).var.get(x);
                }
                for (int y = 0; y < p.pre.size(); y++)
                    for (int z = 0; z < p.pre.get(y).var.size(); z++)
                        if (p.pre.get(y).var.get(z).equals(st))
                            p.pre.get(y).var.set(z, str);
                for (int y = 0; y < q.pre.size(); y++)
                    for (int z = 0; z < q.pre.get(y).var.size(); z++)
                        if (q.pre.get(y).var.get(z).equals(st))
                            q.pre.get(y).var.set(z, str);
            }
        }
        return true;
    }
}
public class InferenceEngine {
    public static void main(String[] args) {
        try (BufferedReader read = new BufferedReader((new FileReader("input.txt")))) {
            int nq = Integer.parseInt(read.readLine());
            String s[] = new String[nq];
            for (int i = 0; i < nq; i++)
                s[i] = read.readLine();
            int nkb = Integer.parseInt(read.readLine());
            KB kb = new KB();
            for (int i = 0; i < nkb; i++)
                kb.add(new Predicate(read.readLine()));
            kb.tabulate();
            BufferedWriter write = new BufferedWriter(new FileWriter("output.txt"));
            for (int i = 0; i < nq; i++) {
                kb.pre=new ArrayList<>();
                Predicate p=new Predicate(s[i]);
                p.negateAll();
                kb.add(p);
                kb.addIndex();
                if (kb.validate(p))
                    write.write("TRUE");
                else
                    write.write("FALSE");
                if (i != nq - 1)
                    write.newLine();
                kb.remove(kb.kb.size()-1);
                kb.kb.remove(kb.kb.size()-1);
            }
            write.close();
        } catch (Exception e) {
            System.out.println("File Not Found" + e.getMessage());
            e.printStackTrace();
        }
    }
}