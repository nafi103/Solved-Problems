#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int mt = 0;
 struct Lazy_Segment_Tree{
    int n;
    vector<int>v,lazy,st;
     Lazy_Segment_Tree(vector<int>&_v,int _n){
        n = _n;
        st.resize(4*n);
        lazy.resize(4*n,0);
        v = _v;
        build(1,1,n);
    }
        void build(int node, int b, int e){
        if(b==e){
            st[node] = v[b];
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        build(left, b, mid);
        build(right, mid+1,e);
        st[node] = min(st[left], st[right]);
    }
        void propagate(int node, int b, int e){
        if(lazy[node] == mt)
            return;
        st[node] += (lazy[node]);
        if(b!=e){
            lazy[2 * node] += lazy[node];
            lazy[2 * node+1] += lazy[node];
        }
        lazy[node] = mt;
    }
        void update(int node, int b, int e, int &l, int &r, int &value){
        propagate(node, b, e);
        if(e<l or b>r) return;
        if(b>=l and e<=r){
            lazy[node] = value;
            propagate(node,b,e);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r,value);
        update(right, mid+1,e,l,r,value);
        st[node] = min(st[left], st[right]);
    }
        int query(int node, int b, int e, int &l, int &r){
        propagate(node, b, e);
        if(e<l or b>r) return inf;
        if(b>=l and e<=r){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        return min(query(left,b,mid,l,r) , query(right,mid+1,e,l,r));
    }
     int query(int l, int r){
        return query(1, 1, n, l, r);
    }
     void update(int l, int r, int val){
        update(1, 1, n, l, r, val);
    }
};
 bool check(string &a){
    stack<char> st;
    for(auto &c: a){
        if(c == '(')
            st.push('(');
        else{
            if(st.empty())
                return false;
            st.pop();
        }
    }
    return st.empty();
}
 void solve()
{
    int n, sa = 0, sb = 0;
    cin >> n;
    string a, b;
    cin >> a >> b;
    for (int i = 0; i < n; i++){
        if(b[i] == '(')
            swap(a[i], b[i]);
    }
    vector<int> va(n + 1), vb(n + 1), pa(n + 1, 0), pb(n + 1, 0);
    for (int i = 0; i < n; i++){
        va[i + 1] = (a[i] == '(' ? 1 : -1);
        vb[i + 1] = (b[i] == '(' ? 1 : -1);
        pa[i + 1] = va[i + 1];
        pb[i + 1] = vb[i + 1];
        if(i){
            pa[i + 1] += pa[i];
            pb[i + 1] += pb[i];
        }
    }
    Lazy_Segment_Tree st1(pa, n), st2(pb, n);
    for (int i = 2; i <= n; i++){
        if(a[i - 1] == b[i - 1])
            continue;
        int qa = st1.query(i, n);
        int qb = st2.query(i, n);
        if(qb < 0 and qa > 1){
            swap(a[i - 1], b[i - 1]);
            st1.update(i, n, -2);
            st2.update(i, n, 2);
        }
        // for (int j = 1; j <= n; j++){
        //     st1.query(j, j);
        //     st2.query(j, j);
        // }
    }
    if(check(a) and check(b)){
        cout << "YES" << endl;
    }else{
        cout << "NO" << endl;
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}