#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int n,temp, x =0;
    cin>>n;
    temp = n;
    int arr[n];
    for(int i=0;i<n;i++)    cin>>arr[i];
    while(temp--){
        int a,cnt =0;
        string str;
        cin>> a>> str;
        for (int i = 0; i < str.size(); i++)
        {
            if(str[i] == 'U')   cnt--;
            if(str[i] == 'D')   cnt++;
        }
        arr[x] += cnt%10;
        if(arr[x] < 0) arr[x] +=10;
        if(arr[x] > 9) arr[x] -=10;
        x++;
    }
    for (int i = 0; i < n; i++)
    {
        cout<<arr[i]<<" ";
    }
    cout<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}