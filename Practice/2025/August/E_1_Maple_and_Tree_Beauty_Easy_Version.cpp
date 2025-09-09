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
int max_level,n, k, l;
vector<int>level_count, pref;
vector<vector<int>>dp;

int f(int i, int j){
    if(i>max_level)
        return 0;
    int &ans = dp[i][j];
    if(ans!=-1)
        return ans;
    ans = 0;
    int uz = k-j, uo = pref[i-1] - uz;
    if(j>=level_count[i])
        ans = 1 + f(i+1,j-level_count[i]);
    if(l-uo>=level_count[i])
        ans = max(ans,1 + f(i+1,j));
    return ans;
}

void solve()
{
    pref.clear();
    dp.clear();
    level_count.clear();
    int ans = -inf;
    cin>>n>>k;
    l = n-k;
    vector<int>parent(n+1,-1),level(n+1,0);
    level_count.assign(n+1,0);
    pref.assign(n+1,0);
    vector<vector<int>>t(n+1);
    for(int i = 2; i<=n; i++){
        int &p = parent[i];
        cin>>p;
        t[p].push_back(i);
        t[i].push_back(p);
    }
    queue<array<int,3>>q;
    q.push({1,-1,0});
    while(!q.empty()){
        auto [node,par,l] = q.front();
        q.pop();
        level[node] = l;
        for(auto &child: t[node]){
            if(child!=par){
                q.push({child,node,l+1});
            }
        }
    }
    max_level = inf;
    level_count[0] = 1, pref[0] = 1;
    for(int i = 2; i<=n; i++){
        level_count[level[i]]++;
        if(sz(t[i])==1)
            max_level = min(max_level,level[i]);
    }
    for(int i = 1; i<=n; i++){
        pref[i] = pref[i-1]+level_count[i];
    }
    dp.assign(max_level+1,vector<int>(k+1,-1));
    if(k)
        ans = max(ans,1+f(1,k-1));
    if(k!=n)
        ans = max(ans,1+f(1,k));
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}