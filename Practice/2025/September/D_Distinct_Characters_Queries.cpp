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
    vector<int> value;

    S(){
        value.assign(26,0);
    }

    S(char val){
        value.assign(26,0);
        value[val-'a']++;
    }
};

S combine(S &a, S &b){
    S res;
    for(int i = 0; i<26; i++){
        res.value[i]=(a.value[i]+b.value[i]);
    }
    return res;
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(string &str){
        n = sz(str);
        t.resize(2*n);
        for(int i = n; i<2*n; i++){
            t[i] = S(str[i-n]);
        }
        build();
    }

    void build(){
        for (int i = n - 1; i > 0; --i) t[i] = combine(t[i<<1], t[i<<1|1]);
    }

    void modify(int p, const S &value) {
        for (t[p += n] = value; p >>= 1; ) t[p] = combine(t[p<<1], t[p<<1|1]);
    }

    int query(int l, int r) {
        S resl, resr;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) resl = combine(resl, t[l++]);
            if (r&1) resr = combine(t[--r], resr);
        }
        int cnt = 0;
        for(int i = 0; i<26; i++){
            if(resl.value[i] or resr.value[i])
                cnt++;
        }
        return cnt;
    }
};

void solve()
{
    string str;
    cin>>str;
    Segment_Tree st(str);
    int q,l,r;
    char c;
    cin>>q;
    while(q--){
        int t;
        cin>>t;
        if(t==1){
            cin>>l>>c;
            l--;
            S val(c);
            st.modify(l,val);
        }else{
            cin>>l>>r;
            l--;
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