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
#define inf 1e13
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
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
using vi = vector<int>;

vector<int>weight,subTreeSize;
vector<vi>t;
vector<vector<vi>>dp;
//dp[i][j][k] = I'm at jth children of i-th node
//              and I can take k childrens from here including i

int dfs(int node){
    subTreeSize[node] = 1;
    for(auto &x: t[node]){
        subTreeSize[node]+=dfs(x);
    }
    return subTreeSize[node];
}

int f(int node, int child_pos, int k){
    if(subTreeSize[node]<k) return -inf;
    if(k==1) return weight[node];
    if(child_pos==sz(t[node])) return -inf;
    if(dp[node][child_pos][k]!=-inf) return dp[node][child_pos][k];
    int ans = -inf;
    for(int j = 0; j<k; j++){
        ans = max(ans, f(t[node][child_pos],0,j) + f(node,child_pos+1,k-j));
    }
    ans = max(ans, f(node,child_pos+1,k));
    return dp[node][child_pos][k] = ans;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int n,k;
    cin>>n>>k;
    weight.resize(n+1);
    t.resize(n+1);
    subTreeSize.resize(n+1,-1);
    dp.resize(n+1);
    for(int i = 2; i<=n; i++){
        int parent;
        cin>>parent;
        t[parent].push_back(i);
    }
    for(int i = 1; i<=n; i++){
        int sz = t[i].size();
        dp[i].assign(sz+1,vi(k+1,-inf));
    }
    dfs(1);
    int ans = -inf, sum = 0;
    for(int i = 1; i<=n; i++) {
        cin>>weight[i];
        if(k==1) ans = max(ans,weight[i]);
        if(k==n) sum+=weight[i];
    }
    if(k==n){
        cout<<sum<<endl;
        return 0;
    }
    if(k==1){
        cout<<ans<<endl;
        return 0;
    }
    for(int i = 1; i<=n; i++){
        if(dp[i][0][k]==-inf) f(i,0,k);
        ans = max(ans,dp[i][0][k]);
    }
    cout<<ans<<endl;
}