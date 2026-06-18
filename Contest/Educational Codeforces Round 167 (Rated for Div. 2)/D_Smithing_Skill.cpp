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

struct Furniture{
    int spend,get;
};


void solve()
{
    int n,m,dp_size = 0,ans = 0;
    cin>>n>>m;
    vector<Furniture>fun(n);
    for(auto &b: fun) {
        cin>>b.spend;
        dp_size = max(dp_size,b.spend+1);
    }
    for(auto &b: fun) cin>>b.get;
    vector<int>min_gap(dp_size,INT_MAX),dp(dp_size),c(m);
    for(auto &b: fun){
        min_gap[b.spend] = min(min_gap[b.spend],b.spend - b.get);
    }
    for(int i = 1; i<dp_size; i++){
        min_gap[i] = min(min_gap[i-1], min_gap[i]);
    }
    for(int i = 0; i<dp_size; i++){
        if(min_gap[i]==INT_MAX){
            dp[i] = 0;
            continue;
        }
        dp[i] = 2+dp[i-min_gap[i]];
    }
    readv(c);
    for(auto &x: c){
        if(x<dp_size){
            ans+=dp[x];
            continue;
        }
        int gap = x-dp_size+1;
        int op = (gap+min_gap[dp_size-1] - 1)/min_gap[dp_size-1];
        ans+=(op*2);
        x-=(op*min_gap[dp_size-1]);
        ans+=dp[x];
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