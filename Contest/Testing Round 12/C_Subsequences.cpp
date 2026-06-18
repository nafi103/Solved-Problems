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
    int value;

    S(int val = 0) : value(val) {}

    void read(){
        cin>>value;
    }
};

S combine(S &a, S &b){
    return S(a.value+b.value);
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(int _n){
        n = _n;
        t.resize(2*n);
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
        return combine(resl, resr).value;
    }
};

void solve()
{
    int n,k;
    cin>>n>>k;
    vector<Segment_Tree> st;
    k++;
    vector<int>v(n);
    for(auto &x: v){
        cin>>x;
        x--;
    }
    if(k>n){
        cout<<0<<endl;
        return;
    }
    for(int i = 0; i<=k; i++){
        st.push_back(Segment_Tree(n));
    }
    for(int i = 0; i<n; i++){
        int &x = v[i];
        for(int j = 2; j<=k; j++){
            S val(st[j-1].query(0,x));
            st[j].modify(x,val);
        }
        st[1].modify(x,S(1));
    }
    cout<<st[k].query(0,n)<<endl;
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