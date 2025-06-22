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
    pair<int,int> value;
    
    S(pair<int,int> val = {0,0}) : value(val) {}
};

void _print(S x){
    cerr<<'['<<x.value.ff<<" "<<x.value.ss<<']';
}

S combine(S &a, S &b){
    return S({a.value.ff+b.value.ff,a.value.ss+b.value.ss});
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(int _n){
        n = _n;
        t.resize(2*n);
    }

    void modify(int p, S value) {
        p+=n;
        for (t[p] = combine(t[p],value); p >>= 1; ) t[p] = combine(t[p<<1], t[p<<1|1]);
    }

    pair<int,int> query(int l, int r) {
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
    int n,m,ans = 0;
    cin>>n>>m;
    vector<array<int,3>>people(n+m);
    for(int i = 0; i<n; i++){
        int x,y;
        cin>>x>>y;
        x--,y--;
        people[i] = {x,y,0};
    }
    for(int i = n; i<n+m; i++){
        int x,y;
        cin>>x>>y;
        x--,y--;
        people[i] = {x,y,1};
    }
    Segment_Tree st(n+m);
    sort(all(people));
    for(auto &[x,y,t]: people){
        pair<int,int> curr_ans = st.query(y,n+m);
        if(t){
            ans+=curr_ans.ff;
            st.modify(y,S({0,1}));
        }else{
            ans+=curr_ans.ss;
            st.modify(y,S({1,0}));
        }
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