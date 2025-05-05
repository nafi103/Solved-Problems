#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
struct minST{
    int n;
    vector<int>t;
    minST(int _n,vector<int>&v){
        n = _n;
        t.resize(2*n);
        for(int i = n; i<2*n; i++){
            t[i] = v[i-n];
        }
        build();
    }
    void build() {
        for (int i = n - 1; i > 0; --i) t[i] = min(t[(i<<1)],t[(i<<1)|1]);        
    }
    void modify(int p, int value) {
        for (t[p += n] = value; p > 1; p >>= 1) t[p>>1] = min(t[p],t[p^1]); 
    }
    int query(int l, int r) {
        int res = inf;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) res = min(res, t[l++]);
            if (r&1) res = min(res, t[--r]);
        }
        return res;
    }
};

struct maxST
{
    int n;
    vector<int>t;
    maxST(int _n,vector<int>&v){
        n = _n;
        t.resize(2*n);
        for(int i = n; i<2*n; i++){
            t[i] = v[i-n];
        }
        build();
    }
    void build() {
        for (int i = n - 1; i > 0; --i) {t[i] = max(t[(i<<1)],t[(i<<1)|1]);}
    }
    void modify(int p, int value) {
        for (t[p += n] = value; p > 1; p >>= 1) t[p>>1] = max(t[p],t[p^1]); 
    }
    int query(int l, int r) {
        int res = -inf;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) res = max(res, t[l++]);
            if (r&1) res = max(res, t[--r]);
        }
        return res;
    }
};



void solve()
{
    int n,q;
    cin>>n>>q;
    vector<int>v(n),remPos(n),revRem(n);
    readv(v);
    for(int i = 0; i<n; i++){
        remPos[i] = v[i] - i;
        revRem[i] = v[i] - (n-i);
    }
    minST l1(n,remPos),l2(n,revRem);
    maxST r1(n,remPos),r2(n,revRem);
    cout<<min(r2.t[1]-l2.t[1], r1.t[1]-l1.t[1])<<endl;
    while(q--){
        int idx, newVal;
        cin>>idx>>newVal;
        idx--;
        r1.modify(idx,newVal-idx);
        l1.modify(idx,newVal-idx);
        l2.modify(idx,newVal - (n-idx));
        r2.modify(idx,newVal - (n-idx));
        cout<<min(r2.t[1]-l2.t[1], r1.t[1]-l1.t[1])<<endl;
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}