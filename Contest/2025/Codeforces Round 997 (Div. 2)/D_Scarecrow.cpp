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
#define inf 4e18+10
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
    int n,k,l;
    cin>>n>>k>>l;
    vector<int>v(n),reach_time(n,-1),reach_pos(n,-1);
    readv(v);
    reach_time[0] = v[0];
    int shift = v[0], pos = k;
    reach_pos[0] = k;
    for(int i = 1; i<n; i++){
        v[i]-=shift;
        if(v[i]>pos){
            shift+=(v[i]-pos);
            reach_time[i] = shift;
            pos+=k;
        }else if(pos-v[i]<k){
            pos = v[i]+k;
        }
        if(reach_time[i]==-1) reach_time[i] = reach_time[i-1];
        reach_pos[i] = pos;
    }
    debug(reach_time) debug(reach_pos)
    vector<vector<int>>dp(n,vector<int>(2,inf));
    for(int i = n-1; i>=0; i--){
        if(i<n-1 and reach_time[i]==reach_time[i+1]){
            dp[i][0] = dp[i+1][0];
            dp[i+1][1] = dp[i+1][1];
            continue;
        }
        dp[i][0] = reach_time[i] + max(0ll,l-reach_pos[i]);
        if(i<n-1) dp[i][1] = min(dp[i+1][0],dp[i+1][1]);
    }
    cout<<min(dp[0][0],dp[0][1])<<endl;
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