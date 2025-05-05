#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
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

int mod;

struct S{
    vector<int>value;

    S() {
        value.assign(4,0);
        value[0] = value[3] = 1;
    }

    S(int val){
        value.assign(4,val);
    }

    S(vector<int> _value){
        value = _value;
    }
    
    void read(){
        for(int i = 0; i<4; i++){
            cin>>value[i];
        }
    }

    void write(){
        for(int i = 0; i<4; i++){
            cout<<value[i]<<" ";
            if(i&1) cout<<endl;
        }
        cout<<endl;
    }
};

S combine(S &a, S &b){
    S result(0);
    result.value[0] = (a.value[0] * b.value[0] + a.value[1]* b.value[2])%mod;
    result.value[1] = (a.value[0] * b.value[1] + a.value[1]* b.value[3])%mod;
    result.value[2] = (a.value[2] * b.value[0] + a.value[3]* b.value[2])%mod;
    result.value[3] = (a.value[2] * b.value[1] + a.value[3]* b.value[3])%mod;
    return result;
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
    cin>>mod>>n>>m;
    Segment_Tree st(n);
    st.place();
    while(m--){
        int l,r;
        cin>>l>>r;
        l--;
        st.query(l,r).write();
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