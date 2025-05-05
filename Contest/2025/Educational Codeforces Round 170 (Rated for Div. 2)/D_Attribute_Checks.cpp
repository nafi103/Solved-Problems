#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

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
vector<vector<int>>dp,st,in,cal;

int calc(int total, int i){
    if(cal[total][i]!=-1) return cal[total][i];
    int s = total-i;
    int got_s = upper_bound(all(st[total]),s) - st[total].begin();
    int got_i = upper_bound(all(in[total]),i) - in[total].begin();
    return cal[total][i] = got_s+got_i;
}


void solve()
{
    int n,m;
    cin>>n>>m;
    st.resize(m+1);in.resize(m+1);
    dp.assign(m+1,vector<int>(m+1,-1));
    cal.assign(m+1,vector<int>(m+1,-1));
    int curr = 0;
    for(int i = 0; i<n; i++){
        int x;
        cin>>x;
        if(x==0) curr++;
        else if(x<0){
            st[curr].pb(abs(x));
        }else{
            in[curr].pb(x);
        }
    }
    for(int i = 0; i<=m; i++){
        sort(all(st[i]));
        sort(all(in[i]));
    }
    int ans = 0;
    for(int i = 0; i<=m; i++){
        for(int j = 0; j<=i; j++){
            calc(i,j);
        }
    }
    dp[0][0] = 0;
    for(int i = 1; i<=m; i++){
        for(int j = 0; j<=i; j++){
            dp[i][j] = cal[i][j]+max(dp[i-1][j],(j?dp[i-1][j-1]:0));
            if(i==m){
                ans = max(ans,dp[i][j]);
            }
        }
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