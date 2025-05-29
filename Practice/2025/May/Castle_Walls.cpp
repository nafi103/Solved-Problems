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

    void modify(int p, int value) {
        for (t[p += n].value += value; p >>= 1; ) t[p] = combine(t[p<<1], t[p<<1|1]);
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

const int red = 0, blue = 1, down = 0, up = 1;

void solve()
{
    int n,m,ans = 0;
    cin>>n>>m;
    vector<vector<int>>cnt(n+m+1,vector<int>(2,0)), prev_pos(n+m+1,vector<int>(2,0));
    vector<array<int,3>>v;
    v.reserve(2*(n+m)+1);
    for(int i = 0; i<n; i++){
        int l,r;
        cin>>l>>r;
        v.push_back({l,1,i});
        v.push_back({r,1,i});
    }
    for(int i = 0; i<m; i++){
        int l,r;
        cin>>l>>r;
        v.push_back({l,0,i});
        v.push_back({r,0,i});
    }
    sort(all(v));
    Segment_Tree incomplete(n+m+1), complete(n+m+1);
    int k = 0;
    for(auto &[pos, t, id]: v){
        cnt[id][t]++;
        if(cnt[id][t]==1){
            if(t==red){
                incomplete.modify(pos,1);
            }
            prev_pos[id][t] = pos;
        }else{
            int i,j;
            if(t==red){
                incomplete.modify(prev_pos[id][t],-1);
                complete.modify(pos,1);
            }
            i = prev_pos[id][t];
            j = pos;
            if(t==blue){
                ans+=(incomplete.query(1,j+1).value + complete.query(i,j+1).value);
            }
        }
        k++;
    }
    cout<<ans<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}