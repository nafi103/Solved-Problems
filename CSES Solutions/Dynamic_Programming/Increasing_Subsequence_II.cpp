#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
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
    int value;

    S(int val = 0) : value(val) {}

    void read(){
        cin>>value;
    }
};

S combine(S &a, S &b){
    return S((a.value+b.value)%mod);
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(int _n){
        n = _n;
        t.resize(2*n);
    }

    void modify(int p, int value) {
        p+=n;
        for (t[p].value = (t[p].value+value)%mod; p >>= 1; ) t[p] = combine(t[p<<1], t[p<<1|1]);
    }

    int query(int l, int r) {
        S resl, resr;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) resl = combine(resl, t[l++]);
            if (r&1) resr = combine(t[--r], resr);
        }
        return combine(resl, resr).value;
    }
};

void solve()
{
    int n;
    cin>>n;
    vector<int>v(n),sv;
    readv(v);
    sv = v;
    sort(all(sv));
    map<int,int> compress;
    for(auto &x: sv){
        if(compress.count(x)==0){
            compress[x] = sz(compress);
        }
    }
    Segment_Tree st(sz(compress));
    for(auto &x: v){
        x = compress[x];
    }
    for(auto &x: v){
        int val = (st.query(0,x) + 1)%mod;
        st.modify(x,val);
    }
    cout<<st.query(0,sz(compress))<<endl;
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