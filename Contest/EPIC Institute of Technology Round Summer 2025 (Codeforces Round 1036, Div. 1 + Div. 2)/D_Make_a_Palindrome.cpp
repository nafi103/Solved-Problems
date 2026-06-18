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

int kth_element(vector<int>v,int k){
    sort(all(v));
    return v[k-1];
}

void solve()
{
    int n,k;
    cin>>n>>k;
    vector<int>v(n);
    readv(v);
    int kth = kth_element(v,k);
    vector<int>new_v;
    new_v.reserve(n);
    for(int i = 0; i<n; i++){
        if(v[i]<=kth)
            new_v.push_back(v[i]);
    }
    int rem = sz(new_v) - k + 1;
    int l = 0, r = sz(new_v) - 1;
    while(rem>=0 and l<=r){
        if(new_v[l]==new_v[r]){
            l++;
            r--;
        }else if(new_v[l]<new_v[r] and new_v[r]==kth){
            r--;
            rem--;
        }else if(new_v[l]>new_v[r] and new_v[l]==kth){
            l++;
            rem--;
        }else{
            break;
        }
    }
    if(rem>=0 and l>r){
        yes;
    }else{
        no;
    }
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