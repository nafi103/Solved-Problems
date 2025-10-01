#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct S{ 
    int pref, suff, sum, mxsub;

    S(int val = -inf){
        sum = pref = suff = sum = mxsub = val;
    }
};

S combine(S &a, S &b){
    S res;
    res.pref = max({a.pref,a.sum+b.pref});
    res.suff = max({b.suff,b.sum+a.suff});
    res.sum = a.sum+b.sum;
    res.mxsub = max({a.mxsub,b.mxsub,a.suff+b.pref});
    return res;
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(vector<int>&v){
        n = sz(v);
        t.resize(2*n);
        for(int i = n; i<2*n; i++){
            t[i] = S(v[i-n]);
        }
        build();
    }

    void build(){
        for (int i = n - 1; i > 0; --i) t[i] = combine(t[i<<1], t[i<<1|1]);
    }

    void modify(int p, S value) {
        for (t[p += n] = value; p >>= 1; ) t[p] = combine(t[p<<1], t[p<<1|1]);
    }

    S query(int l, int r) {
        S resl, resr;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) resl = combine(resl, t[l++]);
            if (r&1) resr = combine(t[--r], resr);
        }
        return combine(resl, resr);
    }
};

void solve()
{
    int n;
    cin>>n;
    vector<int>v(n);
    readv(v);
    Segment_Tree st(v);
    int q,t,x,y;
    cin>>q;
    while(q--){
        cin>>t>>x>>y;
        x--;
        if(!t){
            st.modify(x,S(y));
        }else{
            cout<<st.query(x,y).mxsub<<endl;
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}