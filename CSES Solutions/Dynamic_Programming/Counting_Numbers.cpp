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
int n;
vector<int>num,power_of_nine(19);
vector<vector<vector<int>>>dp;

int f(int pos, int prev, int flag){
    if(pos==n)
        return 1;
    int &ans = dp[pos][prev][flag];
    if(ans!=-1)
        return ans;
    if(!flag)
        return ans = power_of_nine[n-pos];
    ans = 0;
    int r = num[pos];
    for(int i = (pos==0); i<=r; i++){
        if(i!=prev)
            ans += f(pos+1, i, i==r);
    }
    return ans;
}

int findAns(int val){
    num.clear();
    dp.clear();
    while(val){
        num.push_back(val%10);
        val/=10;
    }
    reverse(all(num));
    n = sz(num);
    dp.assign(n,vector<vector<int>>(11,vector<int>(2,-1)));
    int extra = 0;
    for(int i = 0; i<sz(num); i++){
        extra+=power_of_nine[i];
    }
    return f(0,10,1)+extra;
}

void solve()
{
    int a,b;
    cin>>a>>b;
    cout<<findAns(b) - (a?findAns(a-1):0ll)<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    power_of_nine[0] = 1;
    for(int i = 1; i<19; i++){
        power_of_nine[i] = power_of_nine[i-1]*9;
    }
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}