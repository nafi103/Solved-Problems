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
vector<int>dp;
vector<vector<int>>g;

int f(int node){
    if(node==1) return dp[node] = 1;
    if(dp[node]!=-1) return dp[node];
    int &ans = dp[node];
    ans = 0;
    for(auto &child: g[node]){
        ans = max(ans,f(child));
    }
    if(!ans) return INT_MIN;
    return ++ans;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int n,m;
    cin>>n>>m;
    g.resize(n+1);
    dp.assign(n+1,-1);
    for(int i = 1; i<=m; i++){
        int u,v;
        cin>>u>>v;
        g[v].pb(u);
    }
    int Ans = f(n);
    if(Ans<1){
        cout<<"IMPOSSIBLE"<<endl;
        return 0;
    }
    cout<<Ans<<endl;
    vector<int>ans;
    int curr = n;
    while(curr!=1){
        ans.pb(curr);
        for(auto &child:g[curr]){
            if(dp[child]==dp[curr]-1){
                curr = child;
                break;
            }
        }
    }
    ans.pb(1);
    reverse(all(ans));
    writev(ans);
}