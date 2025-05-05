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

vector<vector<int>>t,dp;
vector<pair<int,int>>_ranges;

int f(int node, int op, int parent){
    int &ans = dp[node][op];
    if(ans!=-1)
        return ans;
    ans = 0;
    int x = (op?_ranges[node].ss:_ranges[node].ff);
    for(auto &child: t[node]){
        if(child!=parent){
            ans+=max(f(child,0,node)+abs(x-_ranges[child].ff),f(child,1,node)+abs(x-_ranges[child].ss));
        }
    }
    return ans;
}


void solve()
{
    dp.clear();
    t.clear();
    _ranges.clear();
    int n,u,v;
    cin>>n;
    dp.assign(n+1,vector<int>(2,-1));
    t.resize(n+1);
    _ranges.resize(n+1);
    for(int i = 1; i<=n; i++){
        cin>>_ranges[i].ff>>_ranges[i].ss;
    }
    for(int i = 1; i<n; i++){
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    cout<<max(f(1,0,-1),f(1,1,-1))<<endl;
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