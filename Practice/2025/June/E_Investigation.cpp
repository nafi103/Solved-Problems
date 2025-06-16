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
int dp[10][82][82][2];
int n,k;
vector<int>digits;

void process(int x){
    digits.clear();
    while(x){
        digits.push_back(x%10);
        x/=10;
    }
    n = sz(digits);
    for(int i = 0; i<n; i++){
        for(int j = 0; j<k; j++){
            for(int  l = 0; l<k; l++){
                dp[i][j][l][0] = -1;
                dp[i][j][l][1] = -1;
            }
        }
    }
    reverse(all(digits));
}

int f(int pos, int sum, int d_sum, int flag){
    if(pos==n)
        return (sum==0 and d_sum==0);
    int &ans = dp[pos][sum][d_sum][flag];
    if(ans!=-1)
        return ans;
    ans = 0;
    int r = (flag ? 9 : digits[pos]);
    for(int i = 0; i<=r; i++){
        int new_sum = ((i*(int)pow(10,n-pos-1))%k + sum)%k;
        int new_d_sum = (d_sum + i)%k;
        int new_flag = (i==r? flag : 1);
        ans+=f(pos+1,new_sum, new_d_sum, new_flag);
    }
    return ans;
}

void solve()
{
    int a,b;
    cin>>a>>b>>k;
    if(k>82){
        cout<<0<<endl;
        return;
    }
    process(b);
    int ans_b = f(0,0,0,0);
    process(a-1);
    int ans_a = f(0,0,0,0);
    cout<<ans_b-ans_a<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}