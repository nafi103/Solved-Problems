#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e15 + 10;

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

    Lazy_Segment_Tree(int _n){
        n = _n;
        st.assign(4*n + 4, 0);
        lazy.resize(4*n + 4, 0);
    }
    
    void propagate(int node, int b, int e){
        if(lazy[node]==mt)
            return;
        st[node]+=lazy[node];
        if(b!=e){
            lazy[2*node] += lazy[node];
            lazy[2*node+1] += lazy[node];
        }
        lazy[node] = mt;
    }
    
    void update(int node, int b, int e, int l, int r, int value){
        propagate(node, b, e);
        if(e<l or b>r) return;
        if(b>=l and e<=r){
            lazy[node] += value;
            propagate(node,b,e);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r,value);
        update(right, mid+1,e,l,r,value);
        st[node] = max(st[left],st[right]);
    }
    
    int query(int node, int b, int e, int l, int r){
        propagate(node, b, e);
        if(e<l or b>r) return -inf;
        if(b>=l and e<=r){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        return max(query(left,b,mid,l,r) , query(right,mid+1,e,l,r));
    }
};

void solve()
{
    int n;
    cin >> n;
    vector<int> a(n + 1), b(n + 1), p(n + 1), v(n + 1), tv(n + 1);
    for(int i = 1; i <= n; i++)
        cin >> tv[i];
    for(int i = 1; i <= n; i++){
        cin >> a[i];
        v[i] = tv[a[i]];
    }
    for(int i = 1, x; i <= n; i++){
        cin >> x;
        b[x] = i;
    }
    for(int i = 1; i <= n; i++){
        p[i] = b[a[i]];
    }
    Lazy_Segment_Tree st(n);
    for(int i = 1, s = 0, e = n; i <= n; i++){
        int mx_before = st.query(1, s, e, s, p[i] - 1), curr = st.query(1, s, e, p[i], p[i]);
        if(curr < mx_before)
            st.update(1, s, e, p[i], p[i], max(0ll, mx_before - curr));
        st.update(1, s, e, s, p[i] - 1, v[i]);
    }
    cout << st.query(1, 0, n, 0, n) << endl;
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