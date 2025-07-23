#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1000000
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
int arr[50],pref[51];

void solve()
{
    int sum = 0;
    cin>>n;
    pref[0] = 0;
    for(int i =0; i<n; i++){
        cin>>arr[i];
        sum+=arr[i];
    }
    sort(arr,arr+n,greater<int>());
    for(int i = 0; i<n; i++){
        pref[i+1] = pref[i] + arr[i];
    }
    vector<int>dp_now(sum+1,inf), dp_prev(sum+1,inf);
    dp_prev[0] = 0;
    for(int i = n-1; i>=0; i--){
        for(int j = 0; j<=sum; j++){
            if(j>2*(pref[n]-pref[i]))
                break;
            dp_now[j] = min({dp_prev[j]
            ,(j-2*arr[i]>=0? dp_prev[j-2*arr[i]]: inf),
            (j-arr[i]>=0? arr[i]+dp_prev[j-arr[i]]: inf)});
        }
        dp_prev = dp_now;
    }
    int rem = sum - dp_prev[sum];
    if(rem==0){
        cout<<"impossible"<<endl;
    }else{
        cout<<rem/2<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}