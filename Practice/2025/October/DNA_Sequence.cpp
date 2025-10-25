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
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

pair<int,bool> kmp(string &s, int target){
    int n = sz(s);
    vector<int>pie(n,0);
    bool flag = false;
    for (int i = 1; i < n; i++) {
        int j = pie[i-1];
        while (j > 0 && s[i] != s[j])
            j = pie[j-1];
        if (s[i] == s[j])
            j++;
        pie[i] = j;
        if(pie[i]==target)
            flag = true;
    }
    return {pie[n-1],flag};
}

int r,n;
vector<vector<int>>dp,max_match;
vector<string>new_set;

int f(int i, int mask){
    if(mask==r-1)
        return dp[i][mask] = 0;
    int &ans = dp[i][mask];
    if(ans!=-1)
        return ans;
    ans = inf;
    for(int j = 0; j<n; j++){
        if(mask&(1<<j))
            continue;
        int new_mask = mask|(1<<j);
        ans = min(ans,sz(new_set[j])-max_match[i][j]+f(j,new_mask));
    }
    return ans;
}

void solve()
{
    new_set.clear();
    dp.clear();
    max_match.clear();
    cin>>n;
    vector<string> v(n);
    readv(v);
    vector<bool>take(n,true);
    sort(all(v),[&](string &a, string &b){
        if(sz(a)!=sz(b))
            return sz(a)<sz(b);
        return a<b;
    });
    for(int i = 0; i<n; i++){
        for(int j = 0; j<i; j++){
            if(!take[j])
                continue;
            string tmp = v[j]+v[i];
            auto [val,flag] = kmp(tmp,sz(v[j]));
            if(flag){
                take[j] = false;
            }
        }
    }
    for(int i = 0; i<n; i++){
        if(take[i])
            new_set.push_back(v[i]);
    }
    sort(all(new_set),[&](string &a, string &b){
        if(sz(a)!=sz(b))
            return sz(a)<sz(b);
        return a<b;
    });
    n = sz(new_set);
    max_match.assign(n+1,vector<int>(n+1));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            if(i==j)
                continue;
            string tmp = v[j]+v[i];
            auto [val,flag] = kmp(tmp,sz(v[j]));
            max_match[i][j] = val;
        }
    }
    r = (1<<n);
    dp.assign(n+1,vector<int>(r,-1));
    int ans = f(n,0);
    int i = n, mask = 0;
    string astr = "";
    while(mask!=r-1){
        for(int j = 0; j<n; j++){
            if(mask&(1<<j))
                continue;
            int new_mask = mask|(1<<j);
            if(dp[i][mask]==sz(new_set[j])-max_match[i][j]+dp[j][new_mask]){
                for(int k = max_match[i][j]; k<sz(new_set[j]); k++){
                    astr.push_back(new_set[j][k]);
                }
                i = j;
                mask = new_mask;
                break;
            }
        }
    }
    cout<<astr<<endl;
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