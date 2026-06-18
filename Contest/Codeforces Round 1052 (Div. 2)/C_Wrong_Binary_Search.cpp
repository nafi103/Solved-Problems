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


void solve()
{
    int n;
    cin>>n;
    string str;
    cin>>str;
    if((str[0]=='0' and str[1]=='1') or (str[n-1]=='0' and str[n-2]=='1')){
        cout<<"NO"<<endl;
        return;
    }
    bool flag = true;
    for(int i = 0, j = 1, k=2; k<n; i++,j++,k++){
        if(str[i]=='1' and str[j]=='0' and str[k]=='1'){
            flag = false;
            break;
        }
    }
    if(!flag){
        cout<<"NO"<<endl;
        return;
    }
    cout<<"YES"<<endl;
    vector<int>ans(n);
    iota(all(ans),1);
    int l = 0, r = 0;
    while(l<n){
        while(l<n and str[l]=='1')
            l++;
        r = l;
        while(r<n and str[r]=='0')
            r++;
        if(l<n and l<=r){
            reverse(ans.begin()+l, ans.begin()+r);
        }
        l = r;
    }
    for(auto &x: ans){
        cout<<x<<" ";
    }
    cout<<endl;
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}