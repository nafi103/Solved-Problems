#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
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

/****************************************************************/
vector<int>color;
vector<vector<int>>t,dp;

int f(int node, int col, int par){
    if(dp[node][col]!=-1)
        return dp[node][col];
    if(color[node]!=0 and color[node]!=col)
        return dp[node][col] = 0;
    int &ans = dp[node][col] = 1;
    for(auto &child: t[node]){
        if(child==par)
            continue;
        int sum = 0;
        for(int j = 1; j<4; j++){
            if(j!=col){
                sum = (sum+f(child,j,node))%mod;
            }
        }
        ans = (ans*sum)%mod;
    }
    return ans;
}

void solve()
{
    int n,k;
    cin>>n>>k;
    t.resize(n+1);
    color.assign(n+1,0);
    dp.assign(n+1,vector<int>(4,-1));
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    while(k--){
        int node,col;
        cin>>node>>col;
        color[node] = col;
    }
    if(color[1]!=0){
        cout<<f(1,color[1],-1)<<endl;
    }else{
        int ans = 0;
        for(int i = 1; i<4; i++){
            ans+=f(1,i,-1);
        }
        cout<<ans%mod<<endl;
    }
}

int32_t main()
{
    freopen("barnpainting.in", "r", stdin);
    freopen("barnpainting.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}