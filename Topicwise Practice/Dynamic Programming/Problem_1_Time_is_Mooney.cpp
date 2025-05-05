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

/****************************************************************/

vector<vector<int>>g;
vector<int>gain;

void solve()
{
    int n,m,c,ans = 0;
    cin>>n>>m>>c;
    g.resize(n+1);
    gain.assign(n+1,0ll);
    for(int i = 1; i<=n; i++)
        cin>>gain[i];
    while(m--){
        int u,v;
        cin>>u>>v;
        g[u].pb(v);
    }
    vector<vector<int>>dp(n+1,vector<int>(1001,-1));
    dp[1][0] = 0;
    for(int day = 0; day<1001; day++){
        for(int node = 1; node<=n; node++){
            if(dp[node][day]==-1)
                continue;
            if(day+1<1001){
                for(auto &nbr: g[node]){
                    dp[nbr][day+1] = max(dp[nbr][day+1],dp[node][day]+gain[nbr]);
                }
            }
        }
        ans = max(ans,dp[1][day]-c*day*day);
    }
    cout<<ans<<endl;
}

int32_t main()
{
    freopen("time.in", "r", stdin);
    freopen("time.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}