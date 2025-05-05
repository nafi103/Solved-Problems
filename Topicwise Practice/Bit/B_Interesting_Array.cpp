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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
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

struct S{
    int value;

    S(int val = (1<<30) - 1) : value(val) {}

};

S combine(S &a, S &b){
    return S(a.value&b.value);
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(int _n){
        n = _n;
        t.resize(2*n,S());
    }

    void place(vector<int>&v){
        for(int i = n; i<2*n; i++){
            t[i].value = v[i-n];
        }
    }

    void build(){
        for (int i = n - 1; i > 0; --i) t[i] = combine(t[i<<1], t[i<<1|1]);
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
    int n,m;
    cin>>n>>m;
    Segment_Tree st(n);
    vector<array<int,3>>queries(m);
    vector<int>v(n,0);
    vector<vector<int>>tv(n+1,vector<int>(30,0));
    for(int i = 0; i<m; i++){
        auto &[l,r,q] = queries[i];
        cin>>l>>r>>q;
        l--;
        for(int j = 0; j<30; j++){
            if((1<<j)&q){
                tv[l][j]++;
                tv[r][j]--;
            }
        }
    }
    for(int i = 0; i<n; i++){
        for(int j = 0; j<30; j++){
            if(i) tv[i][j]+=tv[i-1][j];
            if(tv[i][j]>0) v[i]= v[i]|(1<<j);
        }
    }
    st.place(v);
    st.build();
    bool valid = true;
    for(auto &[l,r,q]: queries){
        valid = valid&(st.query(l,r).value==q);
    }
    if(valid){
        cout<<"YES"<<endl;
        writev(v);
    }else{
        cout<<"NO"<<endl;
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
        // google(z);
        solve();
    }
}