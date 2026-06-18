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
    pair<int,int> mx, smx;

    S(){
        mx = {-inf,0};
        smx = {-inf,0};
    }

    S(int val){
        mx = {val,1};
        smx = {-inf,0};
    }

    void read(){
        cin>>mx.first;
        mx.second = 1;
    }
};

void add(pair<int,int>&a, pair<int,int>&b){
    if(a.first==b.first and a.first!=-inf){
        a.second+=b.second;
    }
}

S combine(S &a, S &b){
    S res;
    map<int,int> cnt;
    cnt[a.mx.first]+=a.mx.second;
    cnt[a.smx.first]+=a.smx.second;
    cnt[b.mx.first]+=b.mx.second;
    cnt[b.smx.first]+=b.smx.second;
    res.mx = {(*cnt.rbegin()).first,(*cnt.rbegin()).second};
    cnt.erase(res.mx.first);
    res.smx = {(*cnt.rbegin()).first,(*cnt.rbegin()).second};
    return res;
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(int _n){
        n = _n;
        t.resize(2*n);
    }

    void place(){
        for(int i = n; i<2*n; i++){
            t[i].read();
        }
        build();
    }

    void build(){
        for (int i = n - 1; i > 0; --i) t[i] = combine(t[i<<1], t[i<<1|1]);
    }

    void modify(int p, S value) {
        for (t[p += n] = value; p >>= 1; ) t[p] = combine(t[p<<1], t[p<<1|1]);
    }

    int query(int l, int r) {
        S resl, resr;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) resl = combine(resl, t[l++]);
            if (r&1) resr = combine(t[--r], resr);
        }
        return combine(resl, resr).smx.second;
    }
};

void solve()
{
    int n,q;
    cin>>n>>q;
    Segment_Tree st(n);
    st.place();
    while(q--){
        int t,l,r;
        cin>>t>>l>>r;
        l--;
        if(t==1){
            st.modify(l,S(r));
        }else{
            cout<<st.query(l,r)<<endl;
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