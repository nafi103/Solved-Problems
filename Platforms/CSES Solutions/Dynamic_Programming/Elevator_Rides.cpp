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

void solve()
{
    int n,x;
    cin>>n>>x;
    vector<int> v(n);
    readv(v);
    const pair<int,int> dummy = {0,0};
    vector<pair<int,int>>dp((1<<n),dummy);
    dp[0] = {1,0};
    int r = (1<<n);
    for(int mask = 0; mask<r; mask++){
        for(int i = 0; i<n; i++){
            if(mask&(1<<i))
                continue;
            int newMask = mask|(1<<i),newRide = dp[mask].first, newWeight = dp[mask].second+v[i];
            if(newWeight>x){
                newRide++;
                newWeight = v[i];
            }
            if(dp[newMask].first==0 or dp[newMask].first>newRide
                or (dp[newMask].first==newRide and newWeight<dp[newMask].second)
            ){
                dp[newMask] = {newRide,newWeight};
            }
        }
    }
    cout<<dp[r-1].first<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}