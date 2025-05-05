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


void solve()
{
    int n,m,k;
    cin>>n>>m>>k;
    n*=k, m*=k;
    vector<vector<char>>image(n,vector<char>(m));
    for(int i = 0; i<n; i+=k){
        for(int j = 0; j<m; j+=k){
            cin>>image[i][j];
            for(int r = i; r<i+k; r++){
                for(int c = j; c<j+k; c++){
                    image[r][c] = image[i][j];
                }
            }
        }
    }
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++) cout<<image[i][j];
        cout<<endl;
    }
}

int32_t main()
{
    freopen("cowsignal.in", "r", stdin);
    freopen("cowsignal.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}