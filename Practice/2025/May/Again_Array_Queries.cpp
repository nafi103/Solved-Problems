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
#define inf 1e15+10
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
    int diff, len;
    map<int,int>cnt;
    S(){
        len = 0;
        diff = inf;
        cnt.clear();
    }
    S(int n){
        len = 1;
        diff = inf;
        cnt[n]++;
    }
};

void _print(S &x){
    debug(x.diff)
    debug(x.len)
    debug(x.cnt)
}

S combine(S &left, S &right){
    S res;
    res.len = left.len+right.len;
    if(res.len>1000 or left.diff==0 or right.diff==0){
        res.diff = 0;
        return res;
    }
    res.diff = min(left.diff,right.diff);
    for(auto &[f,s]: left.cnt){
        res.cnt[f]++;
    }
    for(auto &[f,s]: right.cnt){
        res.cnt[f]++;
        if (res.cnt[f] >= 2)  {
            res.diff = 0;
            return res;
        }
    }
    int prev = -inf, mn = inf;
    for(auto &[f,s]: res.cnt){
        mn = min(mn,f-prev);
        prev = f;
    }
    res.diff = mn;
    return res;
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(int _n,vector<int>&v){
        n = _n;
        t.resize(2*n);
        for(int i = n; i<2*n; i++){
            t[i] = S(v[i-n]);
        }
        build();
    }

    void build(){
        for (int i = n - 1; i > 0; --i) t[i] = combine(t[i<<1], t[i<<1|1]);
    }

    int query(int l, int r) {
        if(r-l+1>1000){
            return 0;
        }
        S resl, resr;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) resl = combine(resl, t[l++]);
            if (r&1) resr = combine(t[--r], resr);
        }
        S res = combine(resl, resr);
        return res.diff;
    }
};

void solve()
{
    int n,q;
    cin>>n>>q;
    vector<int>v(n);
    readv(v);
    Segment_Tree st(n,v);
    while(q--){
        int l,r;
        cin>>l>>r;
        r++;
        cout<<st.query(l,r)<<endl;
    }
}

void solve2(){
    int n,q;
    cin>>n>>q;
    vector<int>v(n);
    readv(v);
    while(q--){
        vector<int>tmp;
        int l,r;
        cin>>l>>r;
        if(r-l+1>1000){
            cout<<0<<endl;
            continue;
        }
        for(int i = l; i<=r; i++){
            tmp.push_back(v[i]);
        }
        sort(all(tmp));
        int ans = inf;
        for(int i = 1; i<sz(tmp); i++){
            ans = min(ans,tmp[i]-tmp[i-1]);
        }
        cout<<ans<<endl;
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
        cout<<"Case "<<z<<":\n";
        solve2();
    }
}