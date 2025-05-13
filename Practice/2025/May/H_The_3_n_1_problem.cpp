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

    S(int val = -inf) : value(val) {} //if sum set to -> 0, min -> inf, max -> -inf

    void read(){
        cin>>value;
    }
};

S combine(S &a, S &b){
    return S(max(a.value,b.value)); //change opertation for min,max
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(int _n){
        n = _n;
        t.resize(2*n);
    }

    void place(vector<int>&v){
        for(int i = 0; i<n; i++){
            t[i+n] = S(v[i]);
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

int calc(int n){
    int ans = 1;
    while(n>1){
        if(n&1){
            n = (3*n + 1);
        }else{
            n>>=1;
        }
        ans++;
    }
    return ans;
}


int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int n = 1000010;
    vector<int>v(n);
    v[0] = -inf;
    for(int i = 1; i<n; i++){
        v[i] = calc(i);
    }
    Segment_Tree st(n);
    st.place(v);
    int a,b;
    while(cin>>a>>b){
        cout<<a<<" "<<b<<" "<<st.query(min(a,b), max(a,b)+1).value<<endl;
    }
}