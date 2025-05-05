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

struct DP{
    int value,msb;
    vector<vector<int>>dp;

    DP(int _value){
        value = _value;
        msb = 63 - __builtin_clzll(value);
        dp.resize(msb+1,vector<int>(2,-1));
        f(msb,0);
        value = dp[msb][0];
    }

    int f(int i, int flag){
        if(i<0){
            if(flag) return 1;
            else return 0;
        }
        if(dp[i][flag]!=-1) return dp[i][flag];
        int &ans = dp[i][flag] = 0;
        if(!flag){
            if((1ll<<i)&value) ans = f(i-1,0);
            else ans = f(i-1,0)+f(i-1,1);
        }else{
            ans = 2*f(i-1,1);
        }
        return ans;
    }
};


void solve()
{
    int n;
    cin>>n;
    DP ans(n);
    cout<<ans.value<<endl;
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