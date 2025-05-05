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

int Gcd(int a, int b){
    if(b==0)
        return a;
    return Gcd(b,a%b);
}

int N = 200002;

vector<int>et(N);

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    for (int i = 0; i < N; i++)
    et[i] = i;
    for (int i = 2; i < N; i++) {
        if (et[i] == i) {
            for (int j = i; j < N; j += i)
            et[j] -= et[j] / i;
        }
    }
    et[1] = 2;
    for(int i = 1; i<N; i++)
        et[i]+=et[i-1];
    int n;
    while(cin>>n and n){
        int l = 1, r = N-1, ans = 0;
        while(l<=r){
            int mid = (l+r)/2;
            if(et[mid]<n){
                ans = mid;
                l = mid+1;
            }else{
                r = mid-1;
            }
        }
        int last = et[ans];
        ans++;
        set<int>s;
        for(int i = 0; i<ans; i++){
            if(Gcd(ans,i)==1){
                s.insert(i);
                s.insert(ans-i);
            }
        }
        for(auto &x: s){
            if(++last==n){
                cout<<x<<"/"<<ans<<endl;
                break;
            }
        }
    }
}