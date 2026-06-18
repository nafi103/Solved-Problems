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
vector<int>v;
int n,k;

bool check(int val){
    int rmv = n-val, tk = k;
    for(int i = 0; i<n; i++){
        if(v[i]>tk){
            if(rmv)
                rmv--;
            else{
                if(tk)
                    tk--;
                else return false;
            }
        }
    }
    return true;
}

int bs(int l, int r){
    if(l>r)
        return r;
    int mid = (l+r)/2;
    if(check(mid))
        return bs(mid+1,r);
    else return bs(l,mid-1);
}

void solve()
{
    cin>>n>>k;
    v.resize(n);
    readv(v);
    int mx_take = bs(0,n), rmv = n-mx_take;
    string ans = "";
    for(int i = 0; i<n; i++){
        if(v[i]>k){
            if(rmv){
                rmv--;
                ans.push_back('0');
            }
            else{
                ans.push_back('1');
                k--;
            }
        }else{
            ans.push_back('1');
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}