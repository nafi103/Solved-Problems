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
int ans = 0;
vector<vector<int>>t;
vector<int>level,subtree_size; // tour -> 0==tourism, 1==industry
vector<int>inc;

int dfs1(int node, int par ,int l){
    level[node] = l;
    for(auto &child:t[node]){
        if(child!=par){
            subtree_size[node] += dfs1(child,node,l+1);
        }
    }
    inc.push_back(subtree_size[node] - level[node]);
    return subtree_size[node];
}


void solve()
{
    int n,k,save;
    cin>>n>>k;
    save = k;
    t.resize(n+1);
    level.resize(n+1);
    subtree_size.resize(n+1,1);
    inc.reserve(n);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    dfs1(1,-1,1);
    int ans = 0;
    sort(all(inc));
    int rem = n-k;
    while(rem--){
        ans+=inc.back();
        inc.pop_back();
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
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}