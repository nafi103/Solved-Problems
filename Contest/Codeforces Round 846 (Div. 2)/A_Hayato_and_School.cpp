#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl '\n'
 void solve()
{
    int n;
    cin >> n;
    vector<int> arr(n + 1), v1, v2;
    for (int i = 1; i <= n; i++)
    {
        cin >> arr[i];
        if (arr[i] % 2 == 1)
            v1.push_back(i);
        else
            v2.push_back(i);
    }
    if (v1.size() >= 3)
    {
        cout << "YES" << endl;
        for (int i = 0; i < 3; i++)
        {
            cout << v1[i] << " ";
        }
        cout << endl;
    }
    else if (v1.size() != 0 && v2.size() >= 2)
    {
        cout << "YES" << endl;
        cout << v1[0] << " " << v2[0] << " " << v2[1] << endl;
    }
    else
        cout << "NO" << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}